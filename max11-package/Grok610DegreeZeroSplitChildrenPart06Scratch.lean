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

/-- On `p32 = 0` the order-`70` head is `-1624959306694656 p21` times one
three-term cofactor. -/
def degreeZeroPostCollapseP32ZeroOrderOne610
    (w1 p21 p1 q41 q3 : R) : R :=
  -(38999023360671744 : R) * p1 * p21 * q41 -
    14624633760251904 * p21 ^ 2 * q3 +
    22749430293725184 * p21 ^ 2 * q41 * w1

end DegreeZeroOrderOneHead610

end Max11DegreeRoutes
