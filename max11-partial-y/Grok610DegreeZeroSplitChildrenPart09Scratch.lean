import Grok610DegreeZeroSplitChildrenPart06Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseP32ZeroOrderOne610_factor
    (w1 p21 p1 q41 q3 : R) :
    degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 =
      -(1624959306694656 : R) * p21 *
        (24 * p1 * q41 + 9 * p21 * q3 - 14 * p21 * q41 * w1) := by
  simp only [degreeZeroPostCollapseP32ZeroOrderOne610]
  ring

end DegreeZeroOrderOneHead610

end Max11DegreeRoutes
