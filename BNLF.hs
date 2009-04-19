module BNLF where
import Data.Teams.Graph

w1  = Normal "W1"
w2  = Normal "W2"
wh1 = mkNode Normal "WH1"
wh2 = mkNode Normal "WH2"
r1  = mkNode Reward "R1"
r2  = mkNode Reward "R2"

x  = mkNode Normal "X"
y1 = mkNode Normal "Y1"
y2 = mkNode Normal "Y2"

e  = mkNode Control  "e"
h1 = mkNode Dynamics "h1"
h2 = mkNode Dynamics "h2"
d1 = mkNode Control "d1"
d2 = mkNode Control "d2"
f1 = Dynamics "f1"
f2 = Dynamics "f2"
c1 = mkNode Dynamics "c1"
c2 = mkNode Dynamics "c2"

start = f1 .$. (w1 .|. [] ) ++ f2 .$. (w2 .|. [])
system t = e(t) .$. (x(t) .|. w1 : w2 : map x[1..t-1] ++ map y1[1..t-1]
						      ++ map y2 [1..t-1] )
		++ h1(t).$. (y1(t).|. [x(t)])
		++ h2(t).$. (y2(t).|. [y1(t)])
		++ d1(t).$. (wh1(t).|.map y1[1..t])
		++ d2(t).$. (wh2(t).|.map y2[1..t])
		++ c1(t).$. (r1(t) .|. [w1, wh1(t)])
		++ c2(t).$. (r2(t) .|. [w2, wh2(t)])

stop t = []

bnlf = mkTeamTime start system stop 4
