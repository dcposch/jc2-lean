import Grok610DegreeZeroOrder74Part04Scratch
import Grok610DegreeZeroOrder74Part05Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32P21ZeroOrderFourPlus610_zero
    (w1 a42 p32n p21n p1 p0 s2 u2 b63 q1 lambda : R) :
    degreeZeroPostCollapseP32P21ZeroOrderFourPlus610 0 w1 a42 p32n p21n
        p1 p0 s2 u2 b63 q1 lambda =
      degreeZeroPostCollapseP32P21ZeroOrderFive610 w1 a42 p32n p21n p1
        p0 s2 u2 b63 q1 lambda := by
  simp only [degreeZeroPostCollapseP32P21ZeroOrderFourPlus610,
    degreeZeroPostCollapseP32P21ZeroOrderFive610, zero_mul, mul_zero,
    add_zero, sub_zero]

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
