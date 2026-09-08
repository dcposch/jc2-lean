import Grok610DegreeZeroOrder74Part11Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetOrderTwoPlus610_q41Scale
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32 p21 p1 p0 s2
        u2 b63 q53 (h * q41n) q3 q2 q1 lambda =
      degreeZeroPostCollapseJetOrderTwoPlus610 0 w1 a42 p32 p21 p1 p0
          s2 u2 b63 q53 0 q3 q2 q1 lambda +
        h *
          degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610 h w1 a42
            p32 p21 p1 p0 s2 u2 b63 q53 q41n q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetOrderTwoPlus610,
    degreeZeroPostCollapseQ41ZeroMixedOrderTwoPlus610, zero_mul,
    mul_zero, zero_pow, Nat.ofNat_pos, add_zero, sub_zero]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
