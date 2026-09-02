import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedSixthScratch

/-! # The exact degree boundary for the refined-III `K` quotient

The normalized source controls only the outer (`Y`) degrees.  This file
records the sharp degree estimate that is actually available for the
canonical `K` quotient and combines it with the three vanishing jets on the
deep loaded-row child.  In particular, the estimate is coordinate-dependent;
there is no constant `X`-degree bound in the current source interface.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

section KDegreeAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The exact structural degree budget for
`V' - c E' + H' R`.  It deliberately retains the degrees of the source
coordinates: the normalized `(6,8)` packet supplies no absolute bounds for
them in the base variable. -/
def terminalKDotNextDegreeBudget68
    (H E V c R : k[X]) : ℕ :=
  max (max (V.natDegree - 1)
      (c.natDegree + (E.natDegree - 1)))
    ((H.natDegree - 1) + R.natDegree)

theorem terminalKDotNext_natDegree_le_budget_68
    (H E V c R : k[X]) :
    (terminalKDotNext68 H E V c R).natDegree ≤
      terminalKDotNextDegreeBudget68 H E V c R := by
  have hV : V.derivative.natDegree ≤ V.natDegree - 1 :=
    natDegree_derivative_le V
  have hE : E.derivative.natDegree ≤ E.natDegree - 1 :=
    natDegree_derivative_le E
  have hH : H.derivative.natDegree ≤ H.natDegree - 1 :=
    natDegree_derivative_le H
  have hcE : (c * E.derivative).natDegree ≤
      c.natDegree + (E.natDegree - 1) :=
    (natDegree_mul_le).trans (Nat.add_le_add_left hE _)
  have hHR : (H.derivative * R).natDegree ≤
      (H.natDegree - 1) + R.natDegree :=
    (natDegree_mul_le).trans (Nat.add_le_add_right hH _)
  have hsub : (V.derivative - c * E.derivative).natDegree ≤
      max (V.natDegree - 1) (c.natDegree + (E.natDegree - 1)) :=
    (natDegree_sub_le _ _).trans (max_le_max hV hcE)
  have hadd := natDegree_add_le (V.derivative - c * E.derivative)
    (H.derivative * R)
  dsimp only [terminalKDotNext68, terminalKDotNextDegreeBudget68]
  exact hadd.trans (max_le_max hsub hHR)

/-- Three vanishing ordinary derivatives give exactly a triple linear
factor in characteristic zero. -/
theorem X_sub_C_cube_dvd_of_three_jets_68
    (f : k[X]) (a : k) (hf0 : f.eval a = 0)
    (hf1 : f.derivative.eval a = 0)
    (hf2 : f.derivative.derivative.eval a = 0) :
    (X - C a) ^ 3 ∣ f := by
  have hlin : X - C a ∣ f := by
    rw [dvd_iff_isRoot]
    exact hf0
  obtain ⟨f1, hf⟩ := hlin
  have hf1root : f1.eval a = 0 := by
    have hder := congrArg (fun P : k[X] => P.derivative.eval a) hf
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_C, sub_self,
      zero_mul, one_mul, add_zero] at hder
    simpa using hder.symm.trans hf1
  have hlin1 : X - C a ∣ f1 := by
    rw [dvd_iff_isRoot]
    exact hf1root
  obtain ⟨f2, hf1eq⟩ := hlin1
  have hf2root : f2.eval a = 0 := by
    have hder2 := congrArg
      (fun P : k[X] => P.derivative.derivative.eval a) hf
    rw [hf1eq] at hder2
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      derivative_add, derivative_one, derivative_zero, eval_add, eval_mul,
      eval_sub, eval_one, eval_zero, eval_X, eval_C, sub_self, zero_mul,
      one_mul, mul_zero, add_zero, zero_add] at hder2
    have htwo : (2 : k) * f2.eval a = 0 := by
      linear_combination hder2.symm.trans hf2
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hlin2 : X - C a ∣ f2 := by
    rw [dvd_iff_isRoot]
    exact hf2root
  obtain ⟨f3, hf2eq⟩ := hlin2
  refine ⟨f3, ?_⟩
  rw [hf, hf1eq, hf2eq]
  ring

theorem three_le_natDegree_of_three_jets_68
    (f : k[X]) (a : k) (hf : f ≠ 0)
    (hf0 : f.eval a = 0) (hf1 : f.derivative.eval a = 0)
    (hf2 : f.derivative.derivative.eval a = 0) :
    3 ≤ f.natDegree := by
  obtain ⟨u, hu⟩ := X_sub_C_cube_dvd_of_three_jets_68 f a hf0 hf1 hf2
  have hu0 : u ≠ 0 := by
    intro hzero
    apply hf
    rw [hu, hzero, mul_zero]
  rw [hu, natDegree_mul (pow_ne_zero 3 (X_sub_C_ne_zero a)) hu0,
    natDegree_pow, natDegree_X_sub_C]
  omega

/-- The complete honest conclusion of the degree audit on a canonical
quotient: either `K` vanishes globally, or the deep child has a genuine
triple root and its degree is squeezed only by the coordinate-dependent
budget. -/
def terminalRefinedIIIKDegreeBoundary68
    (H E V c R K : k[X]) (a : k) : Prop :=
  K = 0 ∨
    ((X - C a) ^ 3 ∣ K ∧ 3 ≤ K.natDegree ∧
      K.natDegree + 2 ≤ terminalKDotNextDegreeBudget68 H E V c R)

theorem terminalRefinedIIIKDegreeBoundary68_of_canonical
    (H E V c R K : k[X]) (a : k)
    (hdeg : H.natDegree = 2) (hH : H ≠ 0)
    (hcanonical : H * K = terminalKDotNext68 H E V c R)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0) :
    terminalRefinedIIIKDegreeBoundary68 H E V c R K a := by
  by_cases hK : K = 0
  · exact Or.inl hK
  · right
    have hcube := X_sub_C_cube_dvd_of_three_jets_68 K a hK0 hK1 hK2
    refine ⟨hcube, three_le_natDegree_of_three_jets_68 K a hK hK0 hK1 hK2, ?_⟩
    have hmul : (H * K).natDegree = H.natDegree + K.natDegree :=
      natDegree_mul hH hK
    have hbudget := terminalKDotNext_natDegree_le_budget_68 H E V c R
    rw [← hcanonical, hmul, hdeg] at hbudget
    omega

end KDegreeAlgebra68

section KDegreeSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing form of the exact degree boundary.  The hypotheses are
the two reconstruction equalities exported by the canonical `k₁,k₂`
assembly; no new degree assumption is introduced. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIKDegreeBoundary
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (A0 C0 E0 b1 d1 w1 phi1 k1 K : k[X]) (a : k)
    (hkdef :
      let c0 := terminalCShiftNumerator68 H A0 S.alpha
      let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
        S.epsilon S.eta
      let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
        S.alpha S.gamma S.epsilon S.eta
      k1 = terminalKDotNext68 H E0 V0 c0 R1)
    (hkquot : k1 = H * K)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0) :
    let c0 := terminalCShiftNumerator68 H A0 S.alpha
    let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
      S.epsilon S.eta
    let R1 := terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
      S.alpha S.gamma S.epsilon S.eta
    terminalRefinedIIIKDegreeBoundary68 H E0 V0 c0 R1 K a := by
  dsimp only
  apply terminalRefinedIIIKDegreeBoundary68_of_canonical H E0
    (terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
      S.epsilon S.eta)
    (terminalCShiftNumerator68 H A0 S.alpha)
    (terminalKDotLoadQuotient68 H A0 b1 C0 d1 E0 w1 phi1
      S.alpha S.gamma S.epsilon S.eta) K a hdeg
    (H_ne_zero_of_nonsquare68 (H := H))
  · rw [← hkquot]
    simpa only using hkdef
  · exact hK0
  · exact hK1
  · exact hK2

end KDegreeSource68

end Max11DegreeRoutes
