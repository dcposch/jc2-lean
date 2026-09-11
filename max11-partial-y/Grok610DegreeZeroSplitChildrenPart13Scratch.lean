import Sol610ScaleTwoNonzeroFourteenthPostCollapseHeadSplitScratch
import Grok610DegreeZeroSplitChildrenPart12Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroP32ZeroSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Joint grandchild of the `p32 = 0` child, using the fourth-tail split
together with the order-`70` head. -/
theorem degreeZeroPostCollapseP32Zero_grandchildren610
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hp32 : p32 = 0)
    (hfourteenth :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = 0)
    (horder :
      degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    p21 = 0 ∨ (q41 = 0 ∧ q3 = 0) := by
  have hord :=
    degreeZeroPostCollapseP32ZeroOrderOne610_split w1 p21 p1 q41 q3
      horder
  rcases nonzeroFourteenthPostCollapseJetHead610_p32Zero_split w1 a42
      p32 q53 p21 p1 q41 q3 hfourteenth hp32 with hq41 | hp21
  · rcases hord with hp21 | hlin
    · exact Or.inl hp21
    · have hsimp : 9 * p21 * q3 = 0 := by
        simpa [hq41, mul_zero, zero_mul, sub_zero, add_zero] using hlin
      rcases mul_eq_zero.mp hsimp with hnine | hq3
      · exact Or.inl
          ((mul_eq_zero.mp hnine).resolve_left (by norm_num))
      · exact Or.inr ⟨hq41, hq3⟩
  · exact Or.inl hp21

end DegreeZeroP32ZeroSplit610

end Max11DegreeRoutes
