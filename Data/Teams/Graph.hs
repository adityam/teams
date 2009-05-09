-- (c) Aditya Mahajan <aditya.mahajan@yale.edu>
-- | Directed factor graph representation of sequential teams
module Data.Teams.Graph 
  ( Time
  , Variable (..) , Factor (..) , Node 
  , mkVertex , mkReward , mkNonReward , mkDynamics , mkControl
  , Vertex   (..)
  , Edge , EdgeType (..)
  , (.$.) , (.|.)
  , Team , mkTeam , mkTeamTime , mkTeamTimeBy
  , filterNodes, variables, rewards, factors, controls
  , printTeam , showTeam , graphToDot , printGraph
  , label, labels
  , mdp
  ) where

import qualified Data.Graph.Inductive as G
import qualified Data.GraphViz  as G
import qualified Data.Map as M (fromList)
import Data.Map ((!))
import Data.Maybe (fromJust)
import Data.List (nub, intercalate)
import Text.Printf (printf)

-- | Time
type Time = Int

-- | Variable nodes
data Variable = Reward      String
              | NonReward   String
               deriving (Eq, Ord, Show)

-- | Factor Vertexs
data Factor   = Dynamics    String
              | Control     String
                deriving (Eq, Ord, Show)

-- | Create a sequence of nodes
mkVertex ::  (String -> a) -> String -> Time -> a
mkVertex t s = t . (s ++ ) . show

-- | Create a sequence of nodes of a specific type
mkReward ::  String -> Time -> Variable
mkReward    = mkVertex Reward 

mkNonReward ::  String -> Time -> Variable
mkNonReward = mkVertex NonReward

mkDynamics ::  String -> Time -> Factor
mkDynamics  = mkVertex Dynamics

mkControl ::  String -> Time -> Factor
mkControl   = mkVertex Control

-- | A generic node of a graph
type Node = Either Factor Variable

-- | A type class for defining operations on all nodes
class Vertex a where
  name        ::  a  -> String
  names       :: [a] -> String
  isReward    ::  a  -> Bool
  isNonReward ::  a  -> Bool
  isVariable  ::  a  -> Bool
  isDynamics  ::  a  -> Bool
  isControl   ::  a  -> Bool
  isFactor    ::  a  -> Bool
  attribute   ::  a  -> [G.Attribute]
  -- Default implmentation
  names xs     = "[" ++ intercalate ", " (map name xs) ++ "]"
  isVariable   = or . sequence [isReward, isNonReward]
  isFactor     = or . sequence [isControl, isDynamics]


instance Vertex Variable where
  name (Reward    a) = a
  name (NonReward a) = a
  
  isReward    (Reward    _) = True
  isReward    (NonReward _) = False

  isNonReward (Reward    _) = False
  isNonReward (NonReward _) = True

  isDynamics  _   = False
  isControl   _   = False

  attribute (Reward    a) = [G.Style G.Filled, G.FillColor (G.RGB 0 255 0)
                            , G.Shape G.Circle
                            , G.Label a]
  attribute (NonReward a) = [G.Shape G.Circle
                            , G.Label a]

instance Vertex Factor where
  name (Dynamics a) = a
  name (Control  a) = a

  isDynamics (Dynamics _) = True
  isDynamics (Control  _) = False

  isControl  (Dynamics _) = False
  isControl  (Control  _) = True

  isReward    _ = False
  isNonReward _ = False

  attribute (Dynamics a) = [G.Shape G.Rectangle
                           , G.Label a]
  attribute (Control  a) = [G.Style G.Filled, G.FillColor (G.RGB 255 0 0)
                           , G.Shape G.Rectangle
                           , G.Label a]

instance (Vertex a, Vertex b) => Vertex (Either a b) where
  name        = either name        name
  isReward    = either isReward    isReward
  isNonReward = either isNonReward isNonReward
  isDynamics  = either isDynamics  isDynamics 
  isControl   = either isControl   isControl
  attribute   = either attribute   attribute

-- | An edge in a graph
type Edge     = (Node, Node, EdgeType)

data EdgeType = Influence | Belief deriving (Eq, Ord, Show)

edgeAttribute :: EdgeType -> [G.Attribute]
edgeAttribute _ = []

-- | Infix operators for ease of constructing a graph

(.$.) ::  Factor -> (Variable, [Variable]) -> [Edge]
(.$.) f (x,ys) = (Left f, Right x, Influence) 
                : map (\y -> (Right y, Left f, Influence)) ys

(.|.) ::  Variable -> [Variable] -> (Variable, [Variable])
(.|.) x ys = (x,ys)

infixr 4 .|.
infixr 6 .$.

-- | A sequential team as a directed acyclic factor graph (DAFG)
type Team = G.Gr Node EdgeType

-- | A utility function for creating a DAFG
mkTeam :: [Edge] -> Team
mkTeam es = G.mkGraph nodes edges where
  (nodes,nodeMap) = G.mkNodes G.new . nub . concatMap (\(a,b,_) -> [a,b]) $ es
  edges           = fromJust . G.mkEdges nodeMap $ es 

-- | To make a time homogeneous system
mkTeamTime :: (Time -> [Edge]) -> Time -> Team
mkTeamTime dyn = mkTeamTimeBy [] dyn (const [])

-- As an example, lets consider creating a MDP.
-- (Also available in Data.Teams.Graph.Examples.MDP

x = mkNonReward "x"
u = mkNonReward "u"
r = mkReward    "r"

f = mkDynamics  "f"
g = mkControl   "g"
d = mkDynamics  "d"

dynamics t =  f(t-1).$.( x(t) .|. if t == 1 then [] else [x(t-1)] )
          ++  g(t)  .$.( u(t) .|. map x[1..t] ++ map u[1..t-1]    )
          ++  d(t)  .$.( r(t) .|. [ x(t), u(t) ]                  )

mdp = mkTeamTime dynamics 3
    
-- | To make a time homogeneous system with specific start and stop dynamics
mkTeamTimeBy :: [Edge] -> (Time -> [Edge]) -> (Time -> [Edge]) -> Time -> Team
mkTeamTimeBy start dyn stop horizon = mkTeam nodes where
  nodes = start ++ concatMap dyn [1..horizon] ++ stop horizon

-- As an example, lets consider creating a communication problem with feedback
-- (Also available in Data.Teams.Graph.Examples.CommFeedback)

{-
m     = NonReward "m"
mhat  = NonReward "mhat"
r     = Reward    "r"
h     = Dynamics  "h"
g     = Control   "g"
d     = Dynamics  "d"

x = mkNonReward "x"
y = mkNonReward "y"

f = mkControl  "f"
c = mkDynamics "c"

start      = h .$.( m .|. [] )
dynamics t = f(t) .$. ( x(t) .|. m : map x [1..t-1] ++ map y [1..t-1] )
          ++ c(t) .$. ( y(t) .|. [ x(t) ] )
stop t     = g .$. ( mhat .|. map y [1..t] )
          ++ d .$. (r .|. [m, mhat] )

commfb = mkTeamTimeBy start dynamics stop 3
-}

-- * Utility functions

filterNodes :: (Node -> Bool) -> Team -> [G.Node] -> [G.Node]
filterNodes p team = filter (p . label team) 

selContext ::  Vertex a => (a -> Bool) -> G.Context a b -> Bool
selContext p (_,idx,lab,_) = p lab

selNodes :: (Node -> Bool) -> Team -> [G.Node]
selNodes p = map G.node' . G.gsel (selContext p) 

variables :: Team -> [G.Node]
variables = selNodes isVariable

rewards   ::  Team -> [G.Node]
rewards   = selNodes isReward

controls  ::  Team -> [G.Node] 
controls  = selNodes isControl

factors   ::  Team -> [G.Node]
factors   = selNodes isFactor

-- * Display functions

printTeam :: Team -> IO ()
printTeam = putStr . showTeam

showTeam :: Team -> String
showTeam team = showTeamBy team isDynamics "Dynamics:" ++ "\n"
             ++ showTeamBy team isControl  "Control :" ++ "\n"

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

graphToDot :: Team -> G.DotGraph
graphToDot team = G.graphToDot team [] (attribute.snd) 
             (edgeAttribute. \(_,_,b) -> b)

-- | Print the dot file
printGraph ::  Team -> FilePath -> IO Bool
printGraph team = G.runGraphviz (graphToDot team) G.Pdf 

-- | Useful functions
swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

-- | Extensions of Data.Graph.Inductive

label ::  G.Graph gr => gr a b -> G.Node -> a
label gr = fromJust . G.lab gr

labels :: G.Graph gr => gr a b -> [G.Node] -> [a]
labels = map . label 
