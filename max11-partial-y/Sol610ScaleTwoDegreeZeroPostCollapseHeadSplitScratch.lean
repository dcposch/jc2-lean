import Sol610ScaleTwoDegreeZeroPostCollapseJetScratch
import Sol610ScaleTwoNonzeroFourteenthPostCollapseHeadSplitScratch

/-! # Degree-zero split of the `(6,10)` post-collapse chambers

The degree-zero head supplies the missing bilateral split
`p32 = 0 ∨ q41 = 0`.  Combining it with the fourth-tail head leaves exactly
the two honest same-row chamber refinements recorded below.
-/

noncomputable section

namespace Max11DegreeRoutes

section DegreeZeroPostCollapseHeadSplit610

variable {F : Type*} [Field F] [CharZero F]

/-- Vanishing of the degree-zero source head forces one of its two coordinate
factors to vanish. -/
theorem degreeZeroPostCollapseJetHead610_split
    (p32 q41 : F) (hhead : degreeZeroPostCollapseJetHead610 p32 q41 = 0) :
    p32 = 0 ∨ q41 = 0 := by
  rw [degreeZeroPostCollapseJetHead610] at hhead
  rcases mul_eq_zero.mp hhead with hconstantCube | hq41
  · have hp32cube : p32 ^ 3 = 0 :=
      (mul_eq_zero.mp hconstantCube).resolve_left (by norm_num)
    exact Or.inl
      ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hp32cube)
  · exact Or.inr hq41

/-- Joint chamber split supplied by the degree-zero and fourth-tail heads.
No generic factorization of the eight-term fourth-tail head is asserted. -/
theorem degreeZeroAndFourteenthPostCollapseJetHeads610_chambers
    (w1 a42 p32 q53 p21 p1 q41 q3 : F)
    (hdegree : degreeZeroPostCollapseJetHead610 p32 q41 = 0)
    (hfourteenth :
      nonzeroFourteenthPostCollapseJetHead610 w1 a42 p32 q53 p21 p1 q41
        q3 = 0) :
    (p32 = 0 ∧ (q41 = 0 ∨ p21 = 0)) ∨
      (q41 = 0 ∧
        (p32 = 0 ∨
          10 * p32 ^ 2 * q53 + (18 * p32 * w1 - 27 * p21) * q3 = 0)) := by
  rcases degreeZeroPostCollapseJetHead610_split p32 q41 hdegree with
      hp32 | hq41
  · exact Or.inl ⟨hp32,
      nonzeroFourteenthPostCollapseJetHead610_p32Zero_split
        w1 a42 p32 q53 p21 p1 q41 q3 hfourteenth hp32⟩
  · exact Or.inr ⟨hq41,
      nonzeroFourteenthPostCollapseJetHead610_q41Zero_split
        w1 a42 p32 q53 p21 p1 q41 q3 hfourteenth hq41⟩

#print axioms degreeZeroPostCollapseJetHead610_split
#print axioms degreeZeroAndFourteenthPostCollapseJetHeads610_chambers

end DegreeZeroPostCollapseHeadSplit610

end Max11DegreeRoutes
