import Grok610DegreeZeroSplitChildrenPart04Scratch
import Grok610DegreeZeroSplitChildrenPart06Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 4000000 in
theorem degreeZeroPostCollapseJetOrderOne610_p32Zero
    (w1 a42 p32 p21 p1 q53 q41 q3 u2 : R) (hp32 : p32 = 0) :
    degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53 q41 q3
        u2 =
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 := by
  simp only [degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseP32ZeroOrderOne610, hp32, mul_zero, zero_mul,
    add_zero, sub_zero]
  ring

end DegreeZeroOrderOneHead610

end Max11DegreeRoutes
