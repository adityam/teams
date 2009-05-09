module Data.Teams.Structure
  (
    observations , irrelevant , determined , effective 
  , simplifyAt , simplifyOnce , simplify
  , module Data.Teams.Graph
  ) where

import Data.Teams.Graph
import qualified Data.Graph.Inductive as G
import Data.List (intersect, (\\) )
import Debug.Trace

data Mark = NotMarked | TopMarked | BottomMarked | BothMarked
          deriving (Eq, Ord, Show)

chMark :: Mark -> Mark -> Mark
chMark NotMarked         a       = a
chMark     _           NotMarked = NotMarked
chMark BothMarked        _       = BothMarked
chMark     _         BothMarked  = BothMarked
chMark BottomMarked    TopMarked = BothMarked 
chMark TopMarked    BottomMarked = BothMarked 
chMark BottomMarked BottomMarked = BottomMarked 
chMark TopMarked      TopMarked  = TopMarked 

data Schedule = NotScheduled | TopScheduled | BottomScheduled | BothScheduled
               deriving (Eq, Ord, Show)

chSchedule :: Schedule -> Schedule -> Schedule
chSchedule NotScheduled         a          = a
chSchedule     _            NotScheduled   = NotScheduled
chSchedule BothScheduled        _          = BothScheduled
chSchedule     _           BothScheduled   = BothScheduled
chSchedule BottomScheduled  TopScheduled   = BothScheduled 
chSchedule TopScheduled    BottomScheduled = BothScheduled 
chSchedule BottomScheduled BottomScheduled = BottomScheduled 
chSchedule TopScheduled     TopScheduled   = TopScheduled 

data Visit = Visited | NotVisited
            deriving (Eq, Ord, Show)

data Marked = VMarked Variable Mark Schedule Visit
            | FMarked Factor   Mark Schedule Visit
              deriving (Eq, Ord, Show)
             
mark :: Marked -> Mark
mark (VMarked _ m _ _) = m
mark (FMarked _ m _ _) = m

node  :: Marked -> Node
node (VMarked a _ _ _) = Right a
node (FMarked a _ _ _) = Left  a

schedule :: Marked -> Schedule
schedule (VMarked _ _ s _) = s
schedule (FMarked _ _ s _) = s

visit :: Marked -> Visit
visit (VMarked _ _ _ v) = v
visit (FMarked _ _ _ v) = v

addMark :: Mark -> Marked -> Marked
addMark n (VMarked a m s v) = VMarked a (chMark m n) s v 
addMark n (FMarked a m s v) = FMarked a (chMark m n) s v

addSchedule :: Schedule -> Marked -> Marked
addSchedule n (VMarked a m s v) = VMarked a m (chSchedule s n) v
addSchedule n (FMarked a m s v) = FMarked a m (chSchedule s n) v

addVisit :: Marked -> Marked
addVisit (VMarked a m s _) = VMarked a m s Visited
addVisit (FMarked a m s _) = FMarked a m s Visited

clean :: Marked -> Marked
clean (VMarked a _ _ _) = VMarked a NotMarked NotScheduled NotVisited
clean (FMarked a _ _ _) = FMarked a NotMarked NotScheduled NotVisited

isTopMarked :: Marked -> Bool
isTopMarked n = let m = mark n in (m==TopMarked || m == BothMarked)

isBottomMarked :: Marked -> Bool
isBottomMarked n = let m = mark n in (m==BottomMarked || m == BothMarked)

isScheduled :: Marked -> Bool
isScheduled n = NotScheduled /= schedule n

isVisited :: Marked -> Bool
isVisited n = Visited == visit n

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

type MTeam = G.Gr Marked EdgeType

bayesBall :: Team -> [G.Node] -> [G.Node] -> MTeam
bayesBall team condition reward = doBayesBall condition mteam where
  mteam = G.gmap initialize . G.nmap mkClean $ team
  initialize (pre,idx,lab,suc) = (pre, idx, lab', suc) 
      where lab' = if idx `elem` reward 
                   then addSchedule BottomScheduled lab 
                   else lab

scheduled :: MTeam -> [G.Node]
scheduled = selNodes isScheduled

doBayesBall :: [G.Node] -> MTeam -> MTeam
doBayesBall condition gr = case scheduled gr of
  []    -> gr
  (x:_) -> doBayesBall condition (modify gr)  where
    modify | isFactor . node $ mLabel = modifyFactor
           | otherwise                = modifyVariable
      where  mLabel     = label gr x
             mSchedule  = schedule mLabel

             modifyFactor = case mSchedule of
                BottomScheduled -> markClean . bottomThrough
                TopScheduled    -> markClean . topThrough
                BothScheduled   -> markClean . bothThrough
                NotScheduled    -> error ("Node " ++ show x ++ " not scheduled") 

             modifyVariable = case mSchedule of
                BottomScheduled -> markVisited . bottomVisit
                TopScheduled    -> markVisited . topVisit 
                BothScheduled   -> markVisited . bothVisit  
                NotScheduled    -> error ("Node " ++ show x ++ " not scheduled")

             bottomVisit   | x `elem` condition = id
                           | otherwise          = checkAction . markBottom
             checkAction   | isAction gr x      = id
                           | otherwise          = markTop
             topVisit      | x `elem` condition = markBottom
                           | otherwise          = markTop
             bothVisit     | x `elem` condition = markBottom
                           | otherwise          = markTop . markBottom
               
             markTop    g  | not . isTopMarked . label g $ x = 
                              topThrough (markNode g TopMarked x)
                           | otherwise = g

             markBottom  g | not . isBottomMarked . label g $ x = 
                               bottomThrough (markNode g BottomMarked x)
                           | otherwise = g

             topThrough    g = scheduleNodes TopScheduled    g (G.suc g x)
             bottomThrough g = scheduleNodes BottomScheduled g (G.pre g x)
             bothThrough     = topThrough . bottomThrough

             markVisited g = visitNode  x g 
             markClean   g = cleanNode  x g 

isAction :: MTeam -> G.Node -> Bool
isAction mteam x = case G.pre mteam x of 
  []  -> True
  [y] -> isControl. node . label mteam $ y
  _   -> False

markNode :: MTeam -> Mark -> G.Node -> MTeam
markNode mteam m x = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot mark: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, addMark m lab, suc) G.& gr'

scheduleNode :: Schedule -> G.Node -> MTeam -> MTeam
scheduleNode v x mteam = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot schedule: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, addSchedule v lab, suc) G.& gr'

scheduleNodes ::  Schedule -> MTeam -> [G.Node] -> MTeam
scheduleNodes = foldr . scheduleNode

visitNode :: G.Node -> MTeam -> MTeam
visitNode x mteam = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot schedule: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, addSchedule NotScheduled (addVisit lab), suc) G.& gr'

cleanNode :: G.Node -> MTeam -> MTeam
cleanNode x mteam = case G.match x mteam of
  (Nothing, _ ) -> error ("Node " ++ show x ++ " cannot clean: Not in graph")
  (Just (pre,idx,lab,suc), gr') -> (pre, idx, clean lab, suc) G.& gr'

result :: (Marked -> Bool) -> Team -> [G.Node] -> [G.Node] -> [G.Node]
result p team condition = map fst .filter (p.snd) . G.labNodes 
                         . bayesBall team condition 

irrelevant ::  Team -> [G.Node] -> [G.Node] -> [G.Node]
irrelevant = result (and . sequence [not.isTopMarked, isVariable.node])

observations ::  Team -> [G.Node] -> [G.Node] -> [G.Node]
observations team condition reward = condition `intersect` result isVisited team condition reward

determined :: Team -> [G.Node] -> [G.Node]
determined team var = irrelevant team var (variables team) 

effective :: Team -> [G.Node] -> [G.Node] -> [G.Node]
effective team conditioned reward = (determined team conditioned `intersect`
                                     ancestoral team reward) \\ conditioned

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

simplifyOnce :: Team -> Team 
simplifyOnce team = foldr (flip simplifyAt) team (controls team) where

simplify :: Team -> Team
simplify team = untilEqual . zip stream $ [(1::Int)..] where
  stream = iterate simplifyOnce team
  untilEqual ((a,n):as@((b,_):_)) = trace ("Simplify : Iteration " ++ show n) $
                               if G.equal a b then a
                               else untilEqual as
  untilEqual _ = error "Infinite stream ended. This should not happen"
