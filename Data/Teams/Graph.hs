-- (c) Aditya Mahajan
-- | Factor graph representation of sequential teams
module Data.Teams.Graph where

import qualified Data.Graph.Inductive as G
import qualified Data.Map as M (fromList)
import Data.Map ((!), Map)
import Data.Maybe (fromJust, catMaybes)
import Data.List (nub, intersect, union, (\\), 
                  delete, intercalate, inits, foldl')
import Data.Traversable (traverse)
import Control.Applicative (liftA2)
import Control.Arrow ( (&&&) )
import Control.Monad (liftM2)
import Text.Printf (printf)
import Debug.Trace (trace)

{-
Types of Nodes:
---------------

1. Factor Nodes
   * Dynamic Nodes
   * Control Nodes

2. Variable Nodes
   * Reward Nodes
   * Normal Nodes

3. Belief Nodes
   Probability belief of a set of variable nodes on another set of
   variable  nodes

Types of Edges:
---------------

1. Dependency Edges
   Indicate if a variable node depends on a factor node or indicates if a 
   factor node depdends on a variable node.

2. Belief Edges
   Indicates whether a belief node places belief on a variable node or if a
   belief node is conditioned on a variable node.

3. Temporal Edges
   To indicate a total order. This will be implemented when we are interested in
   a sequential decomposition.
  
-}

-- | Nodes:
data Node      = Dynamics   String | Control      String      
               | Normal     String | Reward       String      
               | BeliefNode String | BeliefFactor String
                                           deriving (Eq, Ord, Show)

-- | Edges:
type Edge      = (Node, Node, EdgeType)           
data EdgeType  = Dependency | BeliefEdge   deriving (Eq, Show)

-- | Graph:
type Team      = G.Gr Node EdgeType
type GraphNode = (G.Node, Node)

{-
I wanted a DSL interface for specifying the team problem. Normally,
system dynamics look like

    f( X | Y,Z )
    g( X | Y,Z )

Haskell does not provide operator overloading, so we specify the above system as

   f .$. ( X .|. [Y,Z] )
   ++ g .$. ( X .|. [Y,Z] )

This is a compromise between the natural way to specify the dynamics, and having
to specify all nodes and edges manually. 

-}

(.$.) :: Node -> (Node, [Node]) -> [(Node, Node)]
(.$.) f (x,ys) = (f,x) : map (\y -> (y,f)) ys

(.|.) :: Node -> [Node] -> (Node, [Node])
(.|.) x ys = (x,ys)

-- The operator (++) has infixr 5. We set infix of (.|.) and (.$.) so that we
-- do not need to specify extra brackets.
infixr 4 .|.
infixr 6 .$.

-- | Create a team problem
mkTeam :: [(Node, Node)] -> Team
mkTeam xs = G.mkGraph nodes edges where
  assoc = flip zip [1..] . nub . concatMap (\(a,b) -> [a,b]) $ xs
  nodes = map (\(a,b) -> (b,a)) assoc
  m     = M.fromList assoc
  edges = map ( \(a,b) -> (m!a, m!b, Dependency) ) xs


{-
Using the above syntax, the variables have to defined as

  x1 = NonReward "X1"
  x2 = NonReward "X2"
  x3 = NonReward "X3"

We need to define one variable for each time instant. To make it simpler, we provide the following interface:

  x = mkNode NonReward "X"

and then use `x 1` instead of `x1`, etc.
-}

mkNode :: (String -> Node) -> String -> Int -> Node
mkNode n s = n . (s++) . show

{-
We also provide a means to specify time homogenous teams for arbitrary time.
Some team problems, most notably communication problems, behave differently for
the first and last time instance. If these are not needed, use mkTeamTime'
-}

mkTeamTime :: [(Node, Node)]          -- First step
           -> (Int -> [(Node, Node)]) -- Time homogeneous
           -> (Int -> [(Node, Node)]) -- Last step
           -> Int                     -- Horizon
           -> Team
mkTeamTime start rest end horizon = mkTeam allNodes where
  allNodes = start ++ concatMap rest [1..horizon] ++ end horizon

mkTeamTime':: (Int -> [(Node, Node)]) -- Time homogeneous
           -> Int                     -- Horizon
           -> Team
mkTeamTime' rest = mkTeamTime [] rest (const [])

-- | Add a belief node at a given control factor
mkBelief :: Team -> G.Node -> [G.Node] -> [G.Node] -> Team
mkBelief team idx from to 
    | isControl currentLabel
                = G.insEdges insEdges . G.insNodes insNodes . 
                  G.delEdges delEdges $ team 
    | otherwise = error $ "mkBelief called on a non Control node: " ++ 
                  name currentLabel
  where
  currentLabel = trace (show (showLabels team [idx], showLabels team to,showLabels team from)) label team idx
  beliefLabel  = printf "P(%s.|.%s)" (names' to) (names' from)
  names'       = showLabels team
  [idx1, idx2] = G.newNodes 2 team
  delEdges     = [] 
                 -- G.edges team `intersect` 
                 -- [ (a, b) | a <- from, b <- futureNodes team isControl idx ]
                 -- ++ [ (a,idx) | a <- from, independent' a ] 
                 -- only if from _|_ futureReward idx || (to, child idx)  
  independent' = independent team (to ++ children team idx)
                 (futureNodes team isReward idx) 
  insNodes     = [(idx1, BeliefNode beliefLabel), (idx2, BeliefFactor "F")]
  insEdges     = (idx2, idx1, Dependency) : (idx1, idx, Dependency) :
                 [ (a, idx2, Dependency) | a <- from ] ++ 
                 [ (a, idx1, BeliefEdge) | a <- from ] ++ 
                 [ (idx1, a, BeliefEdge) | a <- to   ] 
                 -- [ (a, idx2, Dependency) | a <- beliefGrandParents team idx ]


-- * Graph information

-- | get label from node index
label :: Team -> G.Node -> Node
label team = fromJust . G.lab team

-- | filter nodes index and label of the team that whose label satisfies a 
-- | given predicate

filterNodes ::  (Node -> Bool) -> Team -> [G.Node] -> [G.Node]
filterNodes p team = filter (p . label team) 

-- | find the belief edges to a belief node
beliefFrom :: Team -> G.Node -> [G.Node]
beliefFrom team = map fst . filter isBeliefEdge . G.lpre team

-- | find the belief edges from a belief node
beliefTo :: Team -> G.Node -> [G.Node]
beliefTo team = map fst . filter isBeliefEdge . G.lsuc team

-- * Graph relations

-- | find indices of parents from the index of a node
parents :: Team -> G.Node -> [G.Node]
parents = G.pre 

-- | find indices of children from the index of a node
children :: Team -> G.Node -> [G.Node]
children = G.suc 

-- | find indices of descendants from the index of a node
descendants :: Team -> G.Node -> [G.Node]
descendants team idx = idx `delete` G.reachable idx team

-- | find indices of ancestors from the index of a node
ancestors :: Team -> G.Node -> [G.Node]
ancestors team idx = idx `delete` G.reachable idx (G.grev team)

-- | find the indices of the ancestoral set from the indices of a given set.
ancestoral :: Team -> [G.Node] -> [G.Node]
ancestoral team = nub . concatMap (flip G.reachable (G.grev team))

-- | find the indices of future nodes that satisfy a particular predicate
futureNodes :: Team -> (Node -> Bool) -> G.Node -> [G.Node]
futureNodes team p = filter (p . label team) . descendants team

-- | find the indices of past nodes that satisfy a particular predicate
pastNodes :: Team -> (Node -> Bool) -> G.Node -> [G.Node]
pastNodes team p = filter (p . label team) . ancestors team

-- | find the belief parents of a control node
beliefParent :: Team -> G.Node -> Maybe G.Node
beliefParent team idx = let 
   idx' = filterNodes isBeliefNode team . parents team $ idx
   in case idx' of
      []  -> Nothing
      [x] -> Just x
      _   -> error $ "more than one belief Parent at node"
                  ++ (show idx) ++ " parents " ++ (show idx')

-- | find the belief update of the belief node of a control node
beliefUpdate :: Team ->  G.Node -> Maybe G.Node
beliefUpdate team idx = do
   bp <- beliefParent team $ idx 
   let bu = filterNodes isBeliefFactor team . parents team $ bp 
   return (head bu)

-- | find the immediate belief ancestors
beliefGrandParents :: Team -> G.Node -> [G.Node]
beliefGrandParents team idx = filter immediate beliefAncestors where
  beliefAncestors  = filterNodes isBeliefNode team . ancestors team $ idx
  immediate idxAnc = let d = descendants team idxAnc in
                     null d || null (d `intersect` beliefAncestors)

-- | find parents that are known the some future controller
knownParents :: Team -> G.Node -> [G.Node]
knownParents team idx | null future = pa idx
                      | otherwise   = pa idx `intersect` foldr1 union future
        where pa      = parents team 
              future  = map pa . futureNodes team isControl $ idx

-- | find the moral of a graph (by marrying all parents)
moral :: Team -> Team
moral team = G.insEdges insEdges team where
  nodes    = G.nodes team
  edges    = G.edges team
  marry x  = let xs = parents team x in 
             [(n1,n2) | n1 <- xs, n2 <- xs, n1 /= n2, notElem (n1,n2) edges] 
  insEdges = map (\(a,b) -> (a,b,Dependency)) . concatMap marry $ nodes

-- * Indepdence

independent :: Team -> [G.Node] -> [G.Node] -> G.Node -> Bool
independent team conditioned reward idx = all different components where
  different  = liftA2 (||) (notElem idx) (null . intersect reward)
  -- different p = notElem idx p || null $ intersect reward p
  components = G.components . G.delNodes (idx `delete` conditioned) . moral .
               G.delNodes (G.nodes team \\ ancestoral team 
                                          (conditioned ++ reward) ) $ team

-- | remove edges from irrelevant parents to a control node
irrelevant :: Team -> G.Node -> Team
irrelevant team idx = G.delEdges edges team where
  edges        = map (\i -> (i,idx)) . filter independent'. 
                 parents team $ idx
  independent' = independent team (parents team idx ++ children team idx)
                             (futureNodes team isReward idx)

-- | add a belief node to a control node
addBelief :: Team -> G.Node -> Team
addBelief team idx | null to   = team
                   | null from = team
                   | otherwise = mkBelief team idx from to 
  where from = knownParents team idx
        to   = state team idx \\ from

-- | 
rmKnownEdges :: Team -> G.Node -> Team
rmKnownEdges team idx = G.insEdges insEdges . G.delEdges delEdges $ team where
  controls    = filterNodes isControl team (G.nodes team)
  from       :: G.Node -> [G.Node]
  from        = catMaybes . traverse (beliefFrom team) .  beliefParent team 
  currentFrom = from idx
  subset      = null . (\\) currentFrom . from
  edges       = [ ((f,c), (f, fromJust $ beliefUpdate team c, Dependency)) 
                | f <- currentFrom, c <- controls
                , subset c ]
  (delEdges, insEdges) = unzip edges

-- | find state sufficient for future rewards
state :: Team -> G.Node -> [G.Node]
state team idx = filter (not . independent') ancestors' where
  ancestors'  :: [G.Node]
  ancestors'   = pastNodes team isVariable idx
  independent' = independent team ancestors' (futureNodes team isReward idx)

-- * Structural property

-- | Remove irrelevant edges from each control
simplify :: Team -> Team
simplify team = foldr (flip irrelevant) team controls where
  controls = filterNodes isControl team (G.nodes team)

-- | Add belief nodes to each control
modify :: Team -> Team
modify = beliefModify rmKnownEdges . beliefModify addBelief

beliefModify :: (Team -> G.Node -> Team) -> Team -> Team
beliefModify f team = foldl' f team controls where
  controls = filterNodes isControl team (G.nodes team)

-- * Boolean checks for nodes 

-- | check if a given node is a dynamics node
isDynamics :: Node -> Bool
isDynamics (Dynamics _) = True
isDynamics _            = False

-- | check if a given node is a control node
isControl :: Node -> Bool
isControl (Control _) = True
isControl _           = False

isBeliefFactor :: Node -> Bool
isBeliefFactor (BeliefFactor _) = True
isBeliefFactor _                = False

isBeliefNode :: Node -> Bool
isBeliefNode (BeliefNode _) = True
isBeliefNode _              = False

isReward :: Node -> Bool
isReward (Reward _) = True
isReward _          = False

isNormal :: Node -> Bool
isNormal (Normal _) = True
isNormal _          = False

isVariable :: Node -> Bool
isVariable n = any ($n) [isNormal, isReward, isBeliefNode]

-- * Boolean checks for edges :: Edge -> Bool

isDependency :: (G.Node, EdgeType) -> Bool
isDependency (_,Dependency) = True
isDependency _              = False

isBeliefEdge :: (G.Node, EdgeType) -> Bool
isBeliefEdge (_,BeliefEdge) = True
isBeliefEdge _              = False

-- * Show Team

printTeam :: Team -> IO ()
printTeam = putStr . showTeam

showTeam :: Team -> String
showTeam team = showFunctions team isDynamics   "Dynamics:" ++ "\n"
             ++ showFunctions team isControl    "Controls:" ++ "\n"
             ++ showFunctions team isBeliefFactor "Belief:" ++ "\n"

showFunctions :: Team -> (Node -> Bool) -> String -> String
showFunctions team p str = if null eq then "" else unlines (header ++ eq)
  where header = [str, map (const '=') str]
        eq     = map showFactor . filterNodes p team $ (G.nodes team)
        showFactor :: G.Node -> String
        showFactor idx = printf "%s.$.(%s.|.%s)" (names' [idx])
                               (names' (children team idx))
                               (names' (parents  team idx))
        names' = showLabels team

-- | get the labels of a collection of node indices
showLabels ::  Team -> [G.Node] -> String
showLabels team = names . map (label team)

-- | get the name of a node
name :: Node -> String
name (Dynamics     s) = s
name (Control      s) = s
name (Normal       s) = s
name (Reward       s) = s
name (BeliefNode   s) = s
name (BeliefFactor s) = s

-- | get names of a collection of nodes
names :: [Node] -> String
names [x] = name x
names xs = "[" ++ intercalate ", " (map name xs) ++ "]"

