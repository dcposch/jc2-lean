import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Fable610ScaleZeroTwelfthDefectSpeedTPart03Scratch
import Sol610ScaleTwoDegreeZeroLocalPoleScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneHead610

variable {R : Type*} [CommRing R]

/-- The coefficient of `h` in the degree-zero post-collapse quotient. -/
def degreeZeroPostCollapseJetOrderOne610
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) : R :=
  45498860587450368*a42*p21*p32*q41 + 17062072720293888*a42*p32^2*q3 - 49290432303071232*a42*p32^2*q41*w1 - 38999023360671744*p1*p21*q41 - 29249267520503808*p1*p32*q3 + 45498860587450368*p1*p32*q41*w1 - 14624633760251904*p21^2*q3 + 22749430293725184*p21^2*q41*w1 + 28436787867156480*p21*p32^2*q53 + 34124145440587776*p21*p32*q3*w1 - 49290432303071232*p21*p32*q41*w1^2 + 6503598706655232*p32^5 - 7188188044197888*p32^4*u2 - 20537680126279680*p32^3*q53*w1 - 18483912113651712*p32^2*q3*w1^2 + 26014394826620928*p32^2*q41*w1^3

end DegreeZeroOrderOneHead610

end Max11DegreeRoutes
