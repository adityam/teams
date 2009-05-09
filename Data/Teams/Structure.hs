-- (c) Aditya Mahajan <aditya.mahajan@yale.edu>
-- | Structural results for sequential teams

{- 
Description
===========

This module implments an automated algortihm to simplify sequential teams. The
simplification is based on conditional independences. We use the Bayes Ball
algortihm to check conditional independence.

-}

module Data.Teams.Structure where
--   (
--     observations , irrelevant , determined , effective 
--   , simplifyAt , simplifyOnce , simplify
--   , module Data.Teams.Graph
--   ) where

import Data.Teams.Graph
import qualified Data.Graph.Inductive as G
import Data.List (intersect, (\\) )
import Debug.Trace


{-
The Bayes Ball algortihm keeps track of a state for each node. The state
consists of a mark (indicating if it has been visited from top or bottom
before), a schedule (indicating if it was scheduled to be visited from top or
bottom), and a flag (indicating if it has been visited or not). 
-}

-- | Mark
data Mark = NotMarked | TopMarked | BottomMarked | BothMarked
          deriving (Eq, Ord, Show)

-- | Change mark
chMark :: Mark -> Mark -> Mark
chMark NotMarked         a       = a
chMark     _           NotMarked = NotMarked
chMark BothMarked        _       = BothMarked
chMark     _         BothMarked  = BothMarked
chMark BottomMarked    TopMarked = BothMarked 
chMark TopMarked    BottomMarked = BothMarked 
chMark BottomMarked BottomMarked = BottomMarked 
chMark TopMarked      TopMarked  = TopMarked 

-- | Schedule
data Schedule = NotScheduled | TopScheduled | BottomScheduled | BothScheduled
               deriving (Eq, Ord, Show)

-- | Change schedule
chSchedule :: Schedule -> Schedule -> Schedule
chSchedule NotScheduled         a          = a
chSchedule     _            NotScheduled   = NotScheduled
chSchedule BothScheduled        _          = BothScheduled
chSchedule     _           BothScheduled   = BothScheduled
chSchedule BottomScheduled  TopScheduled   = BothScheduled 
chSchedule TopScheduled    BottomScheduled = BothScheduled 
chSchedule BottomScheduled BottomScheduled = BottomScheduled 
chSchedule TopScheduled     TopScheduled   = TopScheduled 

-- | Visit
data Visit = Visited | NotVisited
            deriving (Eq, Ord, Show)

-- | A marked node of a graph
data Marked = VMarked Variable Mark Schedule Visit
            | FMarked Factor   Mark Schedule Visit
              deriving (Eq, Ord, Show)

-- | The mark of a marked node
mark :: Marked -> Mark
mark (VMarked _ m _ _) = m
mark (FMarked _ m _ _) = m

-- | The node label of the marked node
node  :: Marked -> Node
node (VMarked a _ _ _) = Right a
node (FMarked a _ _ _) = Left  a

-- | The scedule of a marked node
schedule :: Marked -> Schedule
schedule (VMarked _ _ s _) = s
schedule (FMarked _ _ s _) = s

-- | The visit status of a marked node
visit :: Marked -> Visit
visit (VMarked _ _ _ v) = v
visit (FMarked _ _ _ v) = v

-- | Add a mark to a marked node
addMark :: Mark -> Marked -> Marked
addMark n (VMarked a m s v) = VMarked a (chMark m n) s v 
addMark n (FMarked a m s v) = FMarked a (chMark m n) s v

-- | Add a schedule to a marked node
addSchedule :: Schedule -> Marked -> Marked
addSchedule n (VMarked a m s v) = VMarked a m (chSchedule s n) v
addSchedule n (FMarked a m s v) = FMarked a m (chSchedule s n) v

-- | Add a visit to a marked node
addVisit :: Marked -> Marked
addVisit (VMarked a m s _) = VMarked a m s Visited
addVisit (FMarked a m s _) = FMarked a m s Visited

-- | Remove all flags from the marked node
clean :: Marked -> Marked
clean (VMarked a _ _ _) = VMarked a NotMarked NotScheduled NotVisited
clean (FMarked a _ _ _) = FMarked a NotMarked NotScheduled NotVisited

-- | Check if a marked node is marked on top
isTopMarked :: Marked -> Bool
isTopMarked n = let m = mark n in (m==TopMarked || m == BothMarked)

-- | Check if a marked node is marked on bottom
isBottomMarked :: Marked -> Bool
isBottomMarked n = let m = mark n in (m==BottomMarked || m == BothMarked)

-- | Check if a marked node is scheduled
isScheduled :: Marked -> Bool
isScheduled n = NotScheduled /= schedule n

-- | Check if a marked node is visited
isVisited :: Marked -> Bool
isVisited n = Visited == visit n

-- | A class to convert a normal graph to a marked graph
class Initializable a where
  mkClean :: a -> Marked

instance Initializable Variable where
  mkClean v@(Reward    _) = VMarked v NotMarked NotScheduled NotVisited
  mkClean v@(NonReward _) = VMarked v NotMarked NotScheduled NotVisited

instance Initializable Factor where
  mkClean f@(Dynamics _) = FMarked f NotMarked NotScheduled NotVisited
  mkClean f@(Control  _) = FMarked f NotMarked NotScheduled NotVisited

instance (Initializable a, Initializable b) => Initializable (Either a b) where
  mkClean (Left  a) = mkClean a
  mkClean (Right a) = mkClean a

-- | A marked gream
type MTeam = G.Gr Marked EdgeType

-- | All scheduled nodes
scheduled :: MTeam -> [G.Node]
scheduled = selNodes isScheduled

-- | The Bayes Ball algorithm
bayesBall :: Team -> [G.Node] -> [G.Node] -> MTeam
bayesBall team condition reward = doBayesBall condition mteam where
  -- Initialize all nodes as neither marked, nor scheduled, nor visited
  -- Then schedule all reward nodes to be visited from bottom.
  mteam = G.gmap initialize . G.nmap mkClean $ team
  initialize (pre,idx,lab,suc) = (pre, idx, lab', suc) 
      where lab' = if idx `elem` reward 
                   then addSchedule BottomScheduled lab 
                   else lab

-- | The main loop of the Bayes Ball algorithm
doBayesBall :: [G.Node] -> MTeam -> MTeam
doBayesBall condition gr = case scheduled gr of
  -- If there are no more scheduled nodes, then we are done.
  []    -> gr
  -- Otherwise we modify the graph and loop again
  (x:_) -> doBayesBall condition (modify gr)  where
    modify | isFactor . node $ mLabel = modifyFactor
           | otherwise                = modifyVariable
      where  mLabel     = label gr x
             mSchedule  = schedule mLabel

             -- If we are a factor node, let the ball pass through
             -- Do not mark the node
             modifyFactor = case mSchedule of
                BottomScheduled -> markClean . bottomThrough
                TopScheduled    -> markClean . topThrough
                BothScheduled   -> markClean . bothThrough
                NotScheduled    -> error ("Node " ++ show x ++ " not scheduled") 

             -- If we are at a variable node, bounce the ball intelligently
             -- Then mark the nodes as visited and not scheduled.
             modifyVariable = case mSchedule of
                BottomScheduled -> markVisited . bottomVisit
                TopScheduled    -> markVisited . topVisit 
                BothScheduled   -> markVisited . bothVisit  
                NotScheduled    -> error ("Node " ++ show x ++ " not scheduled")

             -- When the visit is from bottom, if the node is in the
             -- conditioning nodes, do nothing. Otherwise, if the bottom of the
             -- node is not marked, mark the bottom and schedule all of its
             -- parents (pass the ball). Further, if the node is not a
             -- deterministic node, mark its top and visit all its children
             -- (bounce the ball)
             bottomVisit   | x `elem` condition   = id
                           | otherwise            = checkAction . markBottom
             -- Check if a node is a deterministic node or not. 
             checkAction   | isDeterministic gr x = id
                           | otherwise            = markTop
             -- When the visit is from the top, is the node is in the
             -- conditioning node and its bottom is not marked, mark its bottom
             -- and schedule all of its parents to be visisted (bounce the
             -- ball). Otherwise, if the node is not in the conditioning nodes
             -- and its top is not marked, mark its top and schedule all of its
             -- children (pass the ball)
             topVisit      | x `elem` condition   = markBottom
                           | otherwise            = markTop
             -- When the visit is both from the top and bottom, combine the
             -- actions.
             bothVisit     | x `elem` condition   = markBottom
                           | otherwise            = markTop . markBottom
               
             -- To mark the top. If the top is not marked, mark the top and pass
             -- the ball throgh. Otherwise, swallow the ball.
             markTop    g  | not . isTopMarked . label g $ x = 
                              topThrough (markNode TopMarked x g)
                           | otherwise = g

             -- To mark the bottom. If the bottom is not marked, mark the bottom
             -- and pass the ball throgh. Otherwise, swallow the ball.
             markBottom  g | not . isBottomMarked . label g $ x = 
                               bottomThrough (markNode BottomMarked x g)
                           | otherwise = g

             -- Passing the ball through
             topThrough    g = scheduleNodes TopScheduled    g (G.suc g x)
             bottomThrough g = scheduleNodes BottomScheduled g (G.pre g x)
             bothThrough     = topThrough . bottomThrough

             -- Marking the node visited or clean
             markVisited{- g -} = visitNode  x -- g 
             markClean  {- g -} = cleanNode  x -- g 

-- | Check if a node is deterministic. Currently we simply check if its parent
-- is a control node.
isDeterministic :: MTeam -> G.Node -> Bool
isDeterministic mteam x = case G.pre mteam x of 
  []  -> True
  [y] -> isControl. node . label mteam $ y
  _   -> False

-- | Modify a marked node
modifyNode :: (a -> Marked -> Marked) -> a -> G.Node -> MTeam -> MTeam
modifyNode f m x mteam = case G.match x mteam of
  (Nothing, _ ) -> error ("Cannot modify node " ++ show x ++ " : Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, f m lab, suc) G.& gr'

-- | Mark a node
markNode :: Mark -> G.Node -> MTeam -> MTeam
markNode = modifyNode addMark

-- | Schedule a node
scheduleNode :: Schedule -> G.Node -> MTeam -> MTeam
scheduleNode = modifyNode addSchedule

-- | Schedule a list of nodes
scheduleNodes ::  Schedule -> MTeam -> [G.Node] -> MTeam
scheduleNodes = foldr . scheduleNode 

-- | Visit a node
visitNode :: G.Node -> MTeam -> MTeam
visitNode = modifyNode (\s -> addSchedule s . addVisit) NotScheduled

-- | Clean a node of all marked
cleanNode :: G.Node -> MTeam -> MTeam
cleanNode = modifyNode (const clean) id

-- | Filter out the result from the bayes ball algortihm
result :: (Marked -> Bool) -> Team -> [G.Node] -> [G.Node] -> [G.Node]
result p team condition = map fst . filter (p.snd) . G.labNodes 
                         . bayesBall team condition 

-- | Irrelevant nodes
--   The nodes that have not been visited from their parents are irrelevant
--   (We are not marking factor nodes. If we did that, then we would also need
--   to check if a given node was a variable node or not)
irrelevant ::  Team -> [G.Node] -> [G.Node] -> [G.Node]
irrelevant = result (not.isTopMarked)

-- | Requisite observations
--   The observation nodes are thouse nodes in the condition that are marked as
--   visited
observations ::  Team -> [G.Node] -> [G.Node] -> [G.Node]
observations team condition reward = condition `intersect` 
                                     result isVisited team condition reward

-- | Functionally determined nodes
--   Nodes that are irrelevant when we want to know about all variable nodes
determined :: Team -> [G.Node] -> [G.Node]
determined team var = irrelevant team var (variables team) 

-- | Effectively observed nodes
--   All the ancestors of the reward nodes that are functionally determined by
--   conditioned nodes.
effective :: Team -> [G.Node] -> [G.Node] -> [G.Node]
effective team conditioned reward = (determined team conditioned `intersect`
                                     ancestoral team reward) \\ conditioned

-- | The graph restructuring algorithm of the paper.
simplifyAt ::  Team -> G.Node -> Team
simplifyAt team control = G.insEdges insEdges . G.delEdges delEdges $ team where
  pa = parents  team control
  ch = children team control
  ne = ch ++ pa
  de = descendants team control
  rd = futureNodes team isReward control
  ob = observations team ne rd \\ ch
  ef = effective team pa rd \\ de
  delEdges = map (\ a -> (a, control)) (pa \\ ob)
  insEdges = map (\ a -> (a, control, Influence)) (ef \\ de)

-- | Simplify all nodes of the graph once
simplifyOnce :: Team -> Team 
simplifyOnce team = foldr (flip simplifyAt) team (controls team) where

-- | The graph simplification aglorithm of the paper
--   I believe that this algorithm will always converge. So, I do not stop the
--   loop after a finite number of iterations. If you find an example that does
--   not converge, please let me know.
simplify :: Team -> Team
simplify team = untilEqual . zip stream $ [(1::Int)..] where
  stream = iterate simplifyOnce team
  untilEqual ((a,n):as@((b,_):_)) = trace ("Simplify : Iteration " ++ show n) $
                               if G.equal a b then a
                               else untilEqual as
  untilEqual _ = error "Infinite stream ended. This should not happen"
