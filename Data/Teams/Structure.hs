module Data.Teams.Structure
  (
   Mark, Marked(..)
  , module Data.Teams.Graph
  ) where

import Data.Teams.Graph
import qualified Data.Graph.Inductive as G
import Control.Arrow
import Data.Maybe (fromJust)

data Mark = NotMarked | TopMarked | BotMarked | BothMarked
          deriving (Eq, Ord, Show)

chMark :: Mark -> Mark -> Mark
chMark NotMarked       a          = a
chMark     a         NotMarked    = a
chMark BothMarked      _          = BothMarked
chMark     _         BothMarked   = BothMarked
chMark BotMarked  TopMarked = BothMarked 
chMark TopMarked BotMarked  = BothMarked 
chMark BotMarked  BotMarked  = BotMarked 
chMark TopMarked TopMarked = TopMarked 

data Visit =  NotScheduled | Visited
           | ParentScheduled | ChildScheduled | BothScheduled
              deriving (Eq, Ord, Show)

chVisit NotScheduled         a            = a
chVisit     a           NotScheduled      = a
chVisit Visited            _            = Visited
chVisit     _           Visited         = Visited
chVisit     _           BothScheduled   = BothScheduled
chVisit ChildScheduled  ParentScheduled = BothScheduled 
chVisit ParentScheduled ChildScheduled  = BothScheduled 
chVisit ChildScheduled  ChildScheduled  = ChildScheduled 
chVisit ParentScheduled ParentScheduled = ParentScheduled 

data Marked = VMarked Variable Mark Visit
            | FMarked Factor   Mark Visit
              deriving (Eq, Ord, Show)
             
mark :: Marked -> Mark
mark (VMarked _ m _) = m
mark (FMarked _ m _) = m

node  :: Marked -> Node
node (VMarked a _ _) = Right a
node (FMarked a _ _) = Left  a

visit :: Marked -> Visit
visit (VMarked _ _ v) = v
visit (FMarked _ _ v) = v

addMark :: Mark -> Marked -> Marked
addMark n (VMarked a m v) = VMarked a (chMark m n) v
addMark n (FMarked a m v) = FMarked a (chMark m n) v

addVisit :: Visit -> Marked -> Marked
addVisit n (VMarked a m v) = VMarked a m (chVisit v n)
addVisit n (FMarked a m v) = FMarked a m (chVisit v n)

isTopMarked :: Marked -> Bool
isTopMarked n = let m = mark n in (m==TopMarked || m == BothMarked)

isBotMarked :: Marked -> Bool
isBotMarked n = let m = mark n in (m==BotMarked || m == BothMarked)

class Initializable a where
  mkClean :: a -> Marked

instance Initializable Variable where
  mkClean v@(Reward    _) = VMarked v NotMarked NotScheduled
  mkClean v@(NonReward _) = VMarked v NotMarked NotScheduled

instance Initializable Factor where
  mkClean f@(Dynamics _) = FMarked f NotMarked NotScheduled
  mkClean f@(Control  _) = FMarked f NotMarked NotScheduled

instance (Initializable a, Initializable b) => Initializable (Either a b) where
  mkClean (Left  a) = mkClean a
  mkClean (Right a) = mkClean a

type MTeam = G.Gr Marked EdgeType

bayesBall :: Team -> [G.Node] -> [G.Node] -> MTeam
bayesBall team condition reward = doBayesBall condition mteam reward where
  -- Initialize all nodes to be not visited and not marked
  -- Initialize all reward  nodes to be visited from child
  initialize (pre,idx,lab,suc) = (pre, idx, lab', suc) 
      where lab' = if idx `elem` reward then addVisit ChildScheduled lab else lab
  mteam = G.gmap initialize . G.nmap mkClean $ team

doBayesBall :: [G.Node] -> MTeam -> [G.Node] -> MTeam
doBayesBall condition gr (x:xs) = doBayesBall condition gr' (xs++extra) where
  (gr', extra) = loop (gr, [])
  loop = case visit . label gr $ x of
    Visited          -> id
    ChildScheduled   -> childVisit  
    ParentScheduled  -> parentVisit 
    BothScheduled    -> bothVisit  
    NotScheduled     -> error ("Node " ++ show x ++ " not scheduled")

    where  childVisit  | x `elem` condition = id
                       | otherwise          = markTop . checkAction
           checkAction | isAction gr x      = id
                       | otherwise          = markBottom
           parentVisit | x `elem` condition = markTop
                       | otherwise          = markBottom
           bothVisit   = childVisit . parentVisit
           
           markTop    (g,s) | isTopMarked . label g $ x = 
                                let g1 = (markNode g TopMarked x)
                                    s1 = G.pre g1 x
                                    g2 = schedule ChildScheduled g1 s1
                                in  (g2, s++s1)
                            | otherwise       = (g,s)
           markBottom (g,s) | isBotMarked . label g $ x = 
                                let g1 = (markNode g BotMarked x)
                                    s1 = G.pre g1 x
                                    g2 = schedule ParentScheduled g1 s1
                                in  (g2, s++s1)
                            | otherwise       = (g,s)


isAction :: MTeam -> G.Node -> Bool
isAction mteam = isControl. node . label mteam . head . G.pre mteam 

markNode :: MTeam -> Mark -> G.Node -> MTeam
markNode mteam m x = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot be marked: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, addMark m lab, suc) G.& mteam

visitNode :: Visit -> G.Node -> MTeam -> MTeam
visitNode v x mteam = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot be marked: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, addVisit v lab, suc) G.& mteam

schedule :: Visit -> MTeam -> [G.Node] -> MTeam
schedule = foldr . visitNode 

requisite ::  Team -> [G.Node] -> [G.Node] -> [G.Node]
requisite team condition =  map fst .filter (isTopMarked.snd) . G.labNodes 
                            . bayesBall team condition 
