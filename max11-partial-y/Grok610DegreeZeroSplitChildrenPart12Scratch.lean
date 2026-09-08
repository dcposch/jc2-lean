import Grok610DegreeZeroSplitChildrenPart09Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroP32ZeroSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Honest scalar split of the `p32 = 0` order-`70` head. -/
theorem degreeZeroPostCollapseP32ZeroOrderOne610_split
    (w1 p21 p1 q41 q3 : F)
    (hhead :
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    p21 = 0 ∨
      24 * p1 * q41 + 9 * p21 * q3 - 14 * p21 * q41 * w1 = 0 := by
  rw [degreeZeroPostCollapseP32ZeroOrderOne610_factor] at hhead
  rcases mul_eq_zero.mp hhead with hconstant | hcofactor
  · have hp21 : p21 = 0 :=
      (mul_eq_zero.mp hconstant).resolve_left (by norm_num)
    exact Or.inl hp21
  · exact Or.inr hcofactor

end DegreeZeroP32ZeroSplit610

end Max11DegreeRoutes
