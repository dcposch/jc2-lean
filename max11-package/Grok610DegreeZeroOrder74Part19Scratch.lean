import Grok610DegreeZeroOrder74Part11Scratch
import Grok610DegreeZeroOrder74Part10Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610_zero
    (w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 0 w1 a42 p32 p21
        p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda =
      degreeZeroPostCollapseQ41ZeroMixedOrderThree610 w1 a42 p32 p21 p1
        p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610,
    degreeZeroPostCollapseQ41ZeroMixedOrderThree610, zero_mul, mul_zero,
    zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
