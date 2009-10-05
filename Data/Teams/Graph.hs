-- (c) Aditya Mahajan <aditya.mahajan@yale.edu>
-- | This Haskell library implements the algorithm for simplifying sequential
-- teams presented 
--
-- Aditya Mahajan and Sekhar Tatikonda, A graphical modeling approach to
-- simplifying sequential teams, proceedings of 7th International Symposium on
-- Modeling and Optimization in Mobile, Ad Hoc, and Wireless Networks (WiOpt),
-- Control over Communication Channels (ConCom) Workshop, Seoul, South Korea,
-- June 27, 2009.
--
-- The paper can be obtained from
-- <http://pantheon.yale.edu/~am894/publications.html#concom-2009>. See
-- <http://pantheon.yale.edu/~am894/code/teams/> for a usage example.
--
-- A team is a multi-agent stochastic control problem in which all agents have a
-- common objective. A team is sequential if and only if there is a partial
-- order between all the system variables. These partial order relationship can
-- be represented using a directed graph, in particular, using a directed factor
-- graph. The variable nodes of the factor graph represent the system variables
-- and the factor nodes represent the system dynamics and control functions. The
-- structural results for these system are equivalent to simplification of the
-- factor graph. An automated algorithm for graph simplification is presented in
-- the "Data.Teams.Structure" module.


module Data.Teams.Graph 
  ( -- * Classes
  Vertex (..)
  -- * Types
  , Time , Variable (..) , Factor (..) , Node 
  , Edge , EdgeType (..)
  , Team
  -- * Constructors for nodes
  , mkVertex , mkReward , mkNonReward , mkControl
  , mkDeterministic, mkStochastic
  -- * Constructor for edges
  , (.$.) , (.|.)
  -- * Constructors for teams
  , mkTeam , mkTeamTime , mkTeamTimeBy
  -- * Select specific nodes
  , selNodes , variables, rewards, factors, controls
  -- * Graph elements
  , parents , children , ancestors , ancestoral , descendants 
  , futureNodes , pastNodes
  -- * Display functions
  , printTeam , showTeam , graphToDot , printGraph
  -- * Utility functions for "Data.Graph.Inductive"
  , label, labels
  -- * Utility functions for "Control.Monad"
  , onlyif
  ) where

import qualified Data.Graph.Inductive as G
import qualified Data.GraphViz  as G
import Data.Maybe (fromJust)
import Data.List (nub, intercalate, delete)
import Text.Printf (printf)
import Control.Monad (MonadPlus, mzero)

-- | Time
type Time = Int

-- | Variable nodes
data Variable = Reward      String  -- ^ Reward variable node
              | NonReward   String  -- ^ Non reard variable node
               deriving (Eq, Ord, Show)

-- | Factor Vertexs
data Factor   = Deterministic String -- ^ Factor node representing deterministic system dynamics
              | Stochastic    String -- ^ Factor node representing stochastic system dynamics
              | Control       String -- ^ Factor node representing control function
                deriving (Eq, Ord, Show)

-- | Create a sequence of nodes of a specific type
mkVertex ::  (String -> a) -> String -> Time -> a
mkVertex t s = t . (s ++ ) . show

-- | Create a sequence of reward nodes
mkReward ::  String -> Time -> Variable
mkReward    = mkVertex Reward 

-- | Create a sequence of non reward nodes
mkNonReward ::  String -> Time -> Variable
mkNonReward = mkVertex NonReward

-- | Create a sequence of stochastic system dynamics nodes
mkStochastic ::  String -> Time -> Factor
mkStochastic  = mkVertex Stochastic

-- | Create a sequence of deterministic system dynamics nodes
mkDeterministic ::  String -> Time -> Factor
mkDeterministic  = mkVertex Deterministic

-- | Create a sequence of control nodes
mkControl ::  String -> Time -> Factor
mkControl   = mkVertex Control

-- | A generic node of a graph
type Node = Either Factor Variable

-- | A type class for defining operations on all nodes
class Vertex a where
  -- | Name of node @a@
  name            ::  a  -> String
  -- | Name of a list of nodes
  names           :: [a] -> String
  -- | Check if node @a@ is a reward node
  isReward        ::  a  -> Bool
  -- | Check if node @a@ is a non reward node
  isNonReward     ::  a  -> Bool
  -- | Check if node @a@ is a variable node
  isVariable      ::  a  -> Bool
  -- | Check if node @a@ is a stochastic system dynamics
  isStochastic    ::  a  -> Bool
  -- | Check if node @a@ is a deterministic stochastic system dynamics
  isDeterministic ::  a  -> Bool
  -- | Check if node @a@ is a control node
  isControl       ::  a  -> Bool
  -- | Check if node @a@ is a factor node
  isFactor        ::  a  -> Bool
  -- | The attributes of the node. Used to contruct the dot file.
  attribute       ::  a  -> [G.Attribute]
  -- Default implmentation
  names xs     = "[" ++ intercalate ", " (map name xs) ++ "]"
  isVariable   = or . sequence [isReward, isNonReward]
  isFactor     = or . sequence [isControl, isDeterministic, isStochastic]


instance Vertex Variable where
  name (Reward    a) = a
  name (NonReward a) = a
  
  isReward    (Reward    _) = True
  isReward    (NonReward _) = False

  isNonReward (Reward    _) = False
  isNonReward (NonReward _) = True

  isDeterministic _   = False
  isStochastic    _   = False
  isControl       _   = False

  attribute (Reward    a) = [G.Style [G.SItem G.Filled []], G.FillColor (G.RGB 255 204 255)
                            , G.Shape G.Circle
                            , G.Label (G.StrLabel a)]
  attribute (NonReward a) = [G.Shape G.Circle
                            , G.Label (G.StrLabel a)]

instance Vertex Factor where
  name (Deterministic a) = a
  name (Stochastic    a) = a
  name (Control       a) = a

  isDeterministic (Deterministic _) = True
  isDeterministic (Stochastic    _) = False
  isDeterministic (Control       _) = False

  isStochastic (Deterministic _) = False
  isStochastic (Stochastic    _) = True
  isStochastic (Control       _) = False

  isControl (Deterministic _) = False
  isControl (Stochastic    _) = False
  isControl (Control       _) = True

  isReward    _ = False
  isNonReward _ = False

  attribute (Deterministic a) = [G.Shape G.Rectangle
                                , G.Label (G.StrLabel a)]
  attribute (Stochastic    a) = [-- G.Style [G.SItem G.Filled []], G.FillColor (G.RGB 100 255 255)
                                {-,-} G.Shape G.Rectangle
                                , G.Label (G.StrLabel a)]
  attribute (Control       a) = [G.Style [G.SItem G.Filled []], G.FillColor (G.RGB 204 255 255)
                                , G.Shape G.Rectangle
                                , G.Label (G.StrLabel a)]

instance (Vertex a, Vertex b) => Vertex (Either a b) where
  name            = either name        name
  isReward        = either isReward    isReward
  isNonReward     = either isNonReward isNonReward
  isDeterministic = either isDeterministic  isDeterministic
  isStochastic    = either isStochastic  isStochastic
  isControl       = either isControl   isControl
  attribute       = either attribute   attribute

-- | An edge in a graph
type Edge     = (Node, Node, EdgeType)

-- | Currently all edges are Influence edges. Future versions will have
--   belief edges.
data EdgeType = Influence | Belief deriving (Eq, Ord, Show)

-- | Since all edges are Influence edges, we do not differential between the
--   edges
edgeAttribute :: EdgeType -> [G.Attribute]
edgeAttribute _ = []

-- | Used with @(.|.)@ to specify relation between the nodes. For example, if
-- @x@ is a function of @y@ and @z@, we can write
-- 
-- @f.$.(x.|.[y,z])@.

(.$.) ::  Factor -> (Variable, [Variable]) -> [Edge]
(.$.) f (x,ys) = (Left f, Right x, Influence) 
                : map (\y -> (Right y, Left f, Influence)) ys

-- | Used with @(.$.)@ to specify relation between the nodes. For example, if
-- @x@ is a function of @y@ and @z@, we can write
--
-- @f.$.(x.|.[y,z])@.
(.|.) ::  Variable -> [Variable] -> (Variable, [Variable])
(.|.) x ys = (x,ys)

infixr 4 .|.
infixr 6 .$.

onlyif :: MonadPlus m => Bool -> m a -> m a
onlyif p a = if p then a else mzero

-- | A sequential team as a directed acyclic factor graph (DAFG)
type Team = G.Gr Node EdgeType

-- | Construct a DAFG from a set of edges. For example, 
--
-- @
-- f = 'Control' \"f\"
-- x = 'Reward'  \"x\"
-- y = 'NonReward' \"y\"
-- z = 'NonReward' \"z\"
-- g = mkTeam $ f.$.(x.|.[y,z])
-- @
--
mkTeam :: [Edge] -> Team
mkTeam es = G.mkGraph nodes edges where
  (nodes,nodeMap) = G.mkNodes G.new . nub . concatMap (\(a,b,_) -> [a,b]) $ es
  edges           = fromJust . G.mkEdges nodeMap $ es 

{- |To make a time homogeneous system. As an example, an MDP can be created as
follows

@
x = 'mkNonReward' \"x\"
u = 'mkNonReward' \"u\"
r = 'mkReward'    \"r\"

f = 'mkStochastic'  \"f\"
g = 'mkControl'     \"g\"
d = 'mkStochastic'  \"d\"

dynamics t =  f(t-1).$.( x(t) .|. if t == 1 then [] else [x(t-1), u(t-1)] )
          ++  g(t)  .$.( u(t) .|. map x[1..t] ++ map u[1..t-1]    )
          ++  d(t)  .$.( r(t) .|. [ x(t), u(t) ]                  )

mdp = 'mkTeamTime' dynamics 3
@
-}
mkTeamTime :: (Time -> [Edge]) -> Time -> Team
mkTeamTime dyn = mkTeamTimeBy [] dyn (const [])
    
{-  To make a time homogeneous system with specific start and stop dynamics
As an example, a communication system with feedback can be created as
follows.

@
m     = 'NonReward'  \"m\"
mhat  = 'NonReward'  \"mhat\"
r     = 'Reward'     \"r\"
h     = 'Stochastic' \"h\"
g     = 'Control'    \"g\"
d     = 'Stochastic' \"d\"

x = 'mkNonReward' \"x\"
y = 'mkNonReward' \"y\"

f = 'mkControl'    \"f\"
c = 'mkStochastic' \"c\"

start      = h .$.( m .|. [] )
dynamics t = f(t) .$. ( x(t) .|. m : map x [1..t-1] ++ map y [1..t-1] )
          ++ c(t) .$. ( y(t) .|. [ x(t) ] )
stop t     = g .$. ( mhat .|. map y [1..t] )
          ++ d .$. (r .|. [m, mhat] )

commfb = 'mkTeamTimeBy' start dynamics stop 3
-}

mkTeamTimeBy :: [Edge] -> (Time -> [Edge]) -> (Time -> [Edge]) -> Time -> Team
mkTeamTimeBy start dyn stop horizon = mkTeam nodes where
  nodes = start ++ concatMap dyn [1..horizon] ++ stop horizon


-- * Utility functions

-- filterNodes :: (Node -> Bool) -> Team -> [G.Node] -> [G.Node]
-- filterNodes p team = filter (p . label team) 

-- | Select nodes whose label satisfy a particular predicate
selNodes :: G.Graph gr => (a -> Bool) -> gr a b -> [G.Node]
selNodes p = map G.node' . G.gsel (p.G.lab') 

-- | All variable nods
variables :: Team -> [G.Node]
variables = selNodes isVariable

-- | All reward nodes
rewards   ::  Team -> [G.Node]
rewards   = selNodes isReward

-- | All control factors
controls  ::  Team -> [G.Node] 
controls  = selNodes isControl

-- | All factors
factors   ::  Team -> [G.Node]
factors   = selNodes isFactor

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


-- * Display functions

-- | Pretty print the team specification
printTeam :: Team -> IO ()
printTeam = putStr . showTeam

-- | Pretty print the team specification
showTeam :: Team -> String
showTeam team = showTeamBy team isStochastic    "Stochastic:"   ++ "\n"
             ++ showTeamBy team isDeterministic "Deterministic" ++ "\n"
             ++ showTeamBy team isControl       "Control :"     ++ "\n"

showTeamBy :: Team -> (Node -> Bool) -> String -> String
showTeamBy team p str = if null equations 
                        then "" 
                        else unlines (header ++ equations)
  where header    = [str, map (const '=') str]
        equations = map showFactor . filter (p.snd) . G.labNodes $ team
        showFactor (idx,lab) = printf "%s.$.(%s.|.%s)" (name lab)
                                  (names.labels team $ suc)
                                  (names.labels team $ pre)
            where suc = G.suc team idx
                  pre = G.pre team idx


-- * Convert to Graphviz graphs

-- | Convert the graph to a dot file
graphToDot :: Team -> G.DotGraph G.Node
graphToDot team = G.graphToDot True team [] (attribute.snd) 
             (edgeAttribute. \(_,_,b) -> b)

-- | Convert the dot file to a pdf
printGraph ::  Team -> FilePath -> IO Bool
printGraph team = G.runGraphviz (graphToDot team) G.Pdf 

-- | Extensions of Data.Graph.Inductive

-- | Label of a particular node
label ::  G.Graph gr => gr a b -> G.Node -> a
label gr = fromJust . G.lab gr

-- | Labels of a list of nodes
labels :: G.Graph gr => gr a b -> [G.Node] -> [a]
labels = map . label 
