import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedEighthScratch

/-! # The homogeneous ninth loaded row on the refined-III deep child -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

section LoadedNinthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalNinthTripleAt68 (b w e : k[X]) (a : k) : k :=
  (derivative^[9] (b * w * e)).eval a

def terminalNinthPairDeepAt68 (D K : k[X]) (a : k) : k :=
  36 * D.derivative.derivative.eval a *
      (derivative^[7] K).eval a +
    84 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.derivative.eval a +
    126 * D.derivative.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.eval a

theorem eval_ninth_pair_deep_68
    (D K : k[X]) (a : k)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0)
    (hK3 : K.derivative.derivative.derivative.eval a = 0)
    (hK4 : K.derivative.derivative.derivative.derivative.eval a = 0) :
    (derivative^[9] (D * K)).eval a =
      terminalNinthPairDeepAt68 D K a := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    terminalNinthPairDeepAt68, derivative_add, derivative_mul, eval_add,
    eval_mul, eval_ofNat, hD0, hD1, hK0, hK1, hK2, hK3, hK4, zero_mul,
    mul_zero, zero_add, add_zero]
  ring

theorem ninth_derivative_C_mul_H_cube_eq_zero_68
    (H : k[X]) (j : k) (hdeg : H.natDegree = 2) :
    derivative^[9] (C j * H ^ 3) = 0 := by
  have hpow : (H ^ 3).natDegree = 6 := by
    rw [natDegree_pow, hdeg]
  have hbound : (C j * H ^ 3).natDegree < 9 := by
    have hmul : (C j * H ^ 3).natDegree ≤
        (C j).natDegree + (H ^ 3).natDegree := natDegree_mul_le
    have hC : (C j).natDegree = 0 := natDegree_C j
    omega
  exact iterate_derivative_eq_zero hbound

theorem terminalLoadedNinth_of_row_68
    (H b w e D K : k[X]) (j a : k)
    (hdeg : H.natDegree = 2)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0)
    (hK3 : K.derivative.derivative.derivative.eval a = 0)
    (hK4 : K.derivative.derivative.derivative.derivative.eval a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalNinthTripleAt68 b w e a -
        terminalNinthPairDeepAt68 D K a = 0 := by
  have h9 := congrArg (fun P : k[X] => (derivative^[9] P).eval a) hrow
  have hload := ninth_derivative_C_mul_H_cube_eq_zero_68 H j hdeg
  rw [hload] at h9
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    derivative_sub, eval_sub, terminalNinthTripleAt68, eval_zero] at h9
  have hpair := eval_ninth_pair_deep_68 D K a hD0 hD1 hK0 hK1 hK2 hK3 hK4
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    at hpair
  rw [hpair] at h9
  simpa only [terminalNinthTripleAt68, Function.iterate_succ_apply',
    Function.iterate_zero_apply] using h9

def terminalLoadedNinthKFiveZeroRest68
    (b w e D K : k[X]) (a : k) : k :=
  terminalNinthTripleAt68 b w e a -
    36 * D.derivative.derivative.eval a *
      (derivative^[7] K).eval a -
    84 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.derivative.eval a

theorem terminalLoadedNinth_controls_D4K5_68
    (b w e D K : k[X]) (a : k)
    (hload9 : terminalNinthTripleAt68 b w e a -
      terminalNinthPairDeepAt68 D K a = 0) :
    126 * D.derivative.derivative.derivative.derivative.eval a *
        K.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedNinthKFiveZeroRest68 b w e D K a := by
  dsimp only [terminalNinthPairDeepAt68,
    terminalLoadedNinthKFiveZeroRest68] at hload9 ⊢
  linear_combination -hload9

def terminalRefinedIIILoadedNinthDeepChildren68
    (H b w e D K : k[X]) (j a : k) : Prop :=
  K.eval a = 0 ∧ K.derivative.eval a = 0 ∧
    K.derivative.derivative.eval a = 0 ∧
    K.derivative.derivative.derivative.eval a = 0 ∧
    K.derivative.derivative.derivative.derivative.eval a = 0 ∧
    terminalLoadedFifthKZeroRest68 H b w e D K j a = 0 ∧
    terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0 ∧
    terminalLoadedSeventhKTripleZeroRest68 b w e D K a = 0 ∧
    terminalLoadedEighthKFourZeroRest68 b w e D K a = 0 ∧
    ((K.derivative.derivative.derivative.derivative.derivative.eval a = 0 ∧
        terminalLoadedNinthKFiveZeroRest68 b w e D K a = 0) ∨
      (K.derivative.derivative.derivative.derivative.derivative.eval a ≠ 0 ∧
        D.derivative.derivative.derivative.derivative.eval a =
          terminalLoadedNinthKFiveZeroRest68 b w e D K a /
            (126 * K.derivative.derivative.derivative.derivative.derivative.eval a)))

def terminalRefinedIIILoadedEighthKFourSolved68
    (H b w e D K : k[X]) (j a : k) : Prop :=
  K.eval a = 0 ∧ K.derivative.eval a = 0 ∧
    K.derivative.derivative.eval a = 0 ∧
    K.derivative.derivative.derivative.eval a = 0 ∧
    terminalLoadedFifthKZeroRest68 H b w e D K j a = 0 ∧
    terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0 ∧
    terminalLoadedSeventhKTripleZeroRest68 b w e D K a = 0 ∧
    K.derivative.derivative.derivative.derivative.eval a ≠ 0 ∧
    D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedEighthKFourZeroRest68 b w e D K a /
        (70 * K.derivative.derivative.derivative.derivative.eval a)

theorem terminalRefinedIIILoadedNinthDeepChildren68_of_row
    (H b w e D K : k[X]) (j a : k)
    (hdeg : H.natDegree = 2)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0)
    (hK3 : K.derivative.derivative.derivative.eval a = 0)
    (hK4 : K.derivative.derivative.derivative.derivative.eval a = 0)
    (hrest5 : terminalLoadedFifthKZeroRest68 H b w e D K j a = 0)
    (hrest6 : terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0)
    (hrest7 : terminalLoadedSeventhKTripleZeroRest68 b w e D K a = 0)
    (hrest8 : terminalLoadedEighthKFourZeroRest68 b w e D K a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalRefinedIIILoadedNinthDeepChildren68 H b w e D K j a := by
  refine ⟨hK0, hK1, hK2, hK3, hK4, hrest5, hrest6, hrest7, hrest8, ?_⟩
  have hload9 := terminalLoadedNinth_of_row_68 H b w e D K j a hdeg
    hD0 hD1 hK0 hK1 hK2 hK3 hK4 hrow
  have hc := terminalLoadedNinth_controls_D4K5_68 b w e D K a hload9
  by_cases hK5 :
      K.derivative.derivative.derivative.derivative.derivative.eval a = 0
  · left
    refine ⟨hK5, ?_⟩
    rw [hK5, mul_zero] at hc
    exact hc.symm
  · right
    refine ⟨hK5, ?_⟩
    exact (eq_div_iff (mul_ne_zero (by norm_num) hK5)).2 (by
      linear_combination hc)

end LoadedNinthAlgebra68

section LoadedNinthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIILoadedNinthSplit
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (A0 C0 E0 b1 b2 D phi w K : k[X]) (a : k)
    (hb : b1 = H * b2)
    (hW : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hA : A0.eval a ≠ 0) (hB : b2.eval a ≠ 0)
    (hw : w.eval a = 0) (hph : phi.eval a = 0) (hD : D.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hph1 : phi.derivative.eval a = 0)
    (hph2 : phi.derivative.derivative.eval a = 0)
    (hI4 : b2 * phi + C 6 * w * D = 0)
    (hrow : b2 * w * terminalEDerivativeNumerator68 H E0 - D * K =
      C j * H ^ 3)
    (hlower : terminalLowerZeroOne68 H A0 b2 C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0) :
    terminalRefinedIIILoadedNinthDeepChildren68 H b2 w
        (terminalEDerivativeNumerator68 H E0) D K j a ∨
      terminalRefinedIIILoadedEighthKFourSolved68 H b2 w
        (terminalEDerivativeNumerator68 H E0) D K j a ∨
      terminalRefinedIIILoadedSeventhKThreeSolved68 H b2 w
        (terminalEDerivativeNumerator68 H E0) D K j a ∨
      terminalRefinedIIILoadedSixthKTwoSolved68 H b2 w
        (terminalEDerivativeNumerator68 H E0) D K j a ∨
      terminalRefinedIIILoadedFifthSolvedSiblings68 H A0 b2 w
        (terminalEDerivativeNumerator68 H E0) D K S.gamma j a ∨
      (D.derivative.eval a ≠ 0 ∧
        phi.derivative.derivative.derivative.eval a ≠ 0) := by
  have hsource := S.terminalRefinedIIIResultantSourcePacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
  rcases hsource.1.2.2.2.2.2 with hDzero | hDnonzero
  · have hprev := S.terminalRefinedIIILoadedEighthSplit (H := H) hdeg
      A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
        hph1 hph2 hI4 hrow hlower
    rcases hprev with hdeep | hK3 | hK2 | hsiblings | hnonzero
    · dsimp only [terminalRefinedIIILoadedEighthDeepChildren68] at hdeep
      rcases hdeep with
        ⟨hK0, hK1, hK2zero, hK3zero, hrest5, hrest6, hrest7,
          hK4zero | hK4nonzero⟩
      · left
        exact terminalRefinedIIILoadedNinthDeepChildren68_of_row H b2 w
          (terminalEDerivativeNumerator68 H E0) D K j a hdeg hD hDzero.1
            hK0 hK1 hK2zero hK3zero hK4zero.1 hrest5 hrest6 hrest7
              hK4zero.2 hrow
      · right; left
        exact ⟨hK0, hK1, hK2zero, hK3zero, hrest5, hrest6, hrest7,
          hK4nonzero.1, hK4nonzero.2⟩
    · right; right; left
      exact hK3
    · right; right; right; left
      exact hK2
    · right; right; right; right; left
      exact hsiblings
    · exact (hnonzero.1 hDzero.1).elim
  · right; right; right; right; right
    exact hDnonzero

end LoadedNinthSource68

end Max11DegreeRoutes
