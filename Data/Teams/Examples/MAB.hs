-- | Multiaccess broadcast 
-- Based on the example in
--   Aditya Mahajan, Ashutosh Nayyar, and Demosthenis Teneketzis,
--   \"Identifying tractable decentralized problems 
--      on the basis of information structures,\"
--    Proceedings of the 46th annual Allerton conference on 
--    communication, control, and computing, pp. 1440-1449, 
--    Monticello, IL, September 23-26, 2008.

module Data.Teams.Examples.MAB where

import Data.Teams.Structure

x1 = mkNonReward "x1" -- queue length of user 1
x2 = mkNonReward "x2" -- queue length of user 2
u1 = mkNonReward "u1" -- decision of user 1
u2 = mkNonReward "u2" -- decision of user 2
z1 = mkNonReward "z1" -- feedback to user 2 (= x1*u1)
z2 = mkNonReward "z2" -- feedback to user 1 (= x2*u2)
r  = mkReward    "r"

f1 = mkStochastic     "f1"
f2 = mkStochastic     "f2"
g1 = mkControl        "g1"
g2 = mkControl        "g2"
c1 = mkDeterministic  "c1"
c2 = mkDeterministic  "c2"
d  = mkStochastic     "d"

dynamics t = f1(t).$.(x1(t).|. onlyif (t /= 1) [x1(t-1), u1(t-1), z2(t-1)])
          ++ f2(t).$.(x2(t).|. onlyif (t /= 1) [x2(t-1), u2(t-1), z1(t-1)])
          ++ g1(t).$.(u1(t).|. map x1[1..t]   ++ map u1[1..t-1] 
                            ++ map z2[1..t-1])
          ++ g2(t).$.(u2(t).|. map x2[1..t]   ++ map u2[1..t-1] 
                            ++ map z1[1..t-1])
          ++ c1(t).$.(z1(t).|. [x1(t), u1(t)])
          ++ c2(t).$.(z2(t).|. [x2(t), u2(t)])
          ++ d(t) .$.(r(t) .|. [x1(t), x2(t), u1(t), u2(t)])

mab = mkTeamTime dynamics 4

