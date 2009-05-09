-- | Real time source coding 
-- Based on
--      Hans S. Witsenhausen 
--      "On the structure of real-time source coders,"
--      Bell Systems Technical Journal, 
--      vol 58, no 6, pp 1437-1451, July-August 1979

import Data.Teams.Structure 

x  = mkNonReward "x"
x' = mkNonReward "x'"
y  = mkNonReward "y"
m  = mkNonReward "m"
r  = mkReward    "r"

f = mkDynamics "f"
c = mkControl  "c"
g = mkControl  "g"
l = mkControl  "l"
d = mkDynamics "d"

dynamics t | t == 1 = f(1).$.(x(1) .|. [])
                   ++ c(1).$.(y(1) .|. [x(1)])
                   ++ g(1).$.(x'(1).|. [y(1)])
                   ++ l(1).$.(m(1) .|. [y(1)])
                   ++ d(1).$.(r(1) .|. [x(1), x'(1)])
           | otherwise = f(t).$.(x(t) .|. [x(t-1)])
                      ++ c(t).$.(y(t) .|. map x[1..t] ++ map y[1..t-1])
                      ++ g(t).$.(x'(t).|. [y(t), m(t-1)])
                      ++ l(t).$.(m(t) .|. [y(t), m(t-1)])
                      ++ d(t).$.(r(t) .|. [x(t), x'(t)])

rt = mkTeamTime dynamics 4

rt' = simplify rt

