-- | Decentralized MDP
-- Based on an email exchange with Ashutosh Nayyar

module Data.Teams.Examples.DecMdp where
import Data.Teams.Structure 

x  = mkNonReward "x"
u1 = mkNonReward "u1"
u2 = mkNonReward "u2"
r  = mkReward    "r"

f  = mkStochastic "f"
g1 = mkControl    "g1"
g2 = mkControl    "g2"
d  = mkStochastic "d"

dynamics t = f(t).$.(x(t) .|. if t == 1 then [] else [x(t-1), u1(t-1), u2(t-1)])
          ++ g1(t).$.(u1(t) .|. map x[1..t] ++ map u1[1..t-1])
          ++ g2(t).$.(u2(t) .|. map x[1..t] ++ map u2[1..t-1])
          ++ d(t) .$.(r(t) .|. [x(t), u1(t), u2(t)])

decMdp = mkTeamTime dynamics 4

decMdp' = simplify decMdp

