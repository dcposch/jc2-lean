import Grok610DegreeZeroSplitChildrenPart13Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroP32ZeroSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- On the `q41 = 0` child, the fourth-tail split together with the
`p32 = 0` grandchild analysis. -/
theorem degreeZeroPostCollapseQ41Zero_grandchildren610
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hq41 : q41 = 0)
    (hfourteenth :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = 0)
    (horder_of_p32 :
      p32 = 0 →
        degreeZeroPostCollapseP32ZeroOrderOne610 w1 p21 p1 q41 q3 = 0) :
    (p32 = 0 ∧ (p21 = 0 ∨ q3 = 0)) ∨
      10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3 = 0 := by
  rcases nonzeroFourteenthPostCollapseJetHead610_q41Zero_split w1 a42
      p32 q53 p21 p1 q41 q3 hfourteenth hq41 with hp32 | hcof
  · have hord := horder_of_p32 hp32
    have hgrand :=
      degreeZeroPostCollapseP32Zero_grandchildren610 w1 a42 p32 q53 p21
        p1 q41 q3 hp32 hfourteenth hord
    refine Or.inl ⟨hp32, ?_⟩
    rcases hgrand with hp21 | hpair
    · exact Or.inl hp21
    · exact Or.inr hpair.2
  · exact Or.inr hcof

end DegreeZeroP32ZeroSplit610

end Max11DegreeRoutes
