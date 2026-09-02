import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIZeroComponentScratch

/-! # The fifth loaded row and its `K`-jet children -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section LoadedFifthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalFifthTripleMiddleDoubleZeroAt68
    (b w e : k[X]) (a : k) : k :=
  10 * b.derivative.derivative.derivative.eval a *
      w.derivative.derivative.eval a * e.eval a +
    10 * b.derivative.derivative.eval a *
      w.derivative.derivative.derivative.eval a * e.eval a +
    5 * b.derivative.eval a *
      w.derivative.derivative.derivative.derivative.eval a * e.eval a +
    b.eval a * w.derivative.derivative.derivative.derivative.derivative.eval a *
      e.eval a +
    30 * b.derivative.derivative.eval a * w.derivative.derivative.eval a *
      e.derivative.eval a +
    20 * b.derivative.eval a * w.derivative.derivative.derivative.eval a *
      e.derivative.eval a +
    5 * b.eval a * w.derivative.derivative.derivative.derivative.eval a *
      e.derivative.eval a +
    30 * b.derivative.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.eval a +
    10 * b.eval a * w.derivative.derivative.derivative.eval a *
      e.derivative.derivative.eval a +
    10 * b.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.derivative.eval a

def terminalFifthPairLeftZeroAt68 (D K : k[X]) (a : k) : k :=
  D.derivative.derivative.derivative.derivative.derivative.eval a * K.eval a +
    5 * D.derivative.derivative.derivative.derivative.eval a *
      K.derivative.eval a +
    10 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.eval a +
    10 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a +
    5 * D.derivative.eval a *
      K.derivative.derivative.derivative.derivative.eval a

theorem eval_fifth_triple_middle_double_zero_68
    (b w e : k[X]) (a : k) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) :
    (b * w * e).derivative.derivative.derivative.derivative.derivative.eval a =
      terminalFifthTripleMiddleDoubleZeroAt68 b w e a := by
  simp only [terminalFifthTripleMiddleDoubleZeroAt68, derivative_add,
    derivative_mul, eval_add, eval_mul, eval_ofNat, hw, hw1, zero_mul,
    mul_zero, zero_add, add_zero]
  ring

theorem eval_fifth_pair_left_zero_68
    (D K : k[X]) (a : k) (hD : D.eval a = 0) :
    (D * K).derivative.derivative.derivative.derivative.derivative.eval a =
      terminalFifthPairLeftZeroAt68 D K a := by
  simp only [terminalFifthPairLeftZeroAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat, hD, zero_mul, add_zero]
  ring

theorem eval_fifth_C_mul_cube_at_root_68
    (H : k[X]) (j a : k) (ha : H.eval a = 0) :
    (C j * H ^ 3).derivative.derivative.derivative.derivative.derivative.eval a =
      60 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.eval a *
          H.derivative.derivative.eval a ^ 2 := by
  simp [derivative_mul, derivative_pow, ha]
  ring

theorem terminalLoadedFifth_of_row_68
    (H b w e D K : k[X]) (j a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) (hD : D.eval a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFifthPairLeftZeroAt68 D K a =
      60 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.eval a *
          H.derivative.derivative.eval a ^ 2 := by
  have h5 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.eval a) hrow
  simp only [derivative_sub, eval_sub,
    eval_fifth_triple_middle_double_zero_68 b w e a hw hw1,
    eval_fifth_pair_left_zero_68 D K a hD,
    eval_fifth_C_mul_cube_at_root_68 H j a ha] at h5
  exact h5

def terminalLoadedFifthKZeroRest68
    (H b w e D K : k[X]) (j a : k) : k :=
  terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
    10 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.eval a -
    10 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a -
    (60 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.derivative.eval a +
      90 * j * H.derivative.eval a * H.derivative.derivative.eval a ^ 2)

theorem terminalLoadedFifth_KZero_controls_D4K1_68
    (H b w e D K : k[X]) (j a : k)
    (hD1 : D.derivative.eval a = 0) (hK : K.eval a = 0)
    (hload5 : terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFifthPairLeftZeroAt68 D K a =
      60 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.eval a * H.derivative.derivative.eval a ^ 2) :
    5 * D.derivative.derivative.derivative.derivative.eval a *
        K.derivative.eval a =
      terminalLoadedFifthKZeroRest68 H b w e D K j a := by
  dsimp only [terminalFifthPairLeftZeroAt68,
    terminalLoadedFifthKZeroRest68] at hload5 ⊢
  simp only [hD1, hK, mul_zero, zero_mul, add_zero] at hload5
  linear_combination -hload5

def terminalLoadedFifthKNonzeroRest68
    (H A b w e D K : k[X]) (gamma j a : k) : k :=
  terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
    5 * (terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a /
      K.eval a) * K.derivative.eval a -
    10 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.eval a -
    10 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a -
    (60 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.derivative.eval a +
      90 * j * H.derivative.eval a * H.derivative.derivative.eval a ^ 2)

theorem terminalLoadedFifth_KNonzero_controls_D5_68
    (H A b w e D K : k[X]) (gamma j a : k)
    (hD1 : D.derivative.eval a = 0) (hK : K.eval a ≠ 0)
    (hD4 : D.derivative.derivative.derivative.derivative.eval a * K.eval a =
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a)
    (hload5 : terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFifthPairLeftZeroAt68 D K a =
      60 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.eval a * H.derivative.derivative.eval a ^ 2) :
    D.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFifthKNonzeroRest68 H A b w e D K gamma j a / K.eval a := by
  have hD4' : D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a /
        K.eval a := (eq_div_iff hK).2 hD4
  apply (eq_div_iff hK).2
  dsimp only [terminalFifthPairLeftZeroAt68,
    terminalLoadedFifthKNonzeroRest68] at hload5 ⊢
  rw [hD4'] at hload5
  simp only [hD1, zero_mul, add_zero] at hload5
  linear_combination -hload5

def terminalRefinedIIILoadedFifthZeroChildren68
    (H A b w e D K : k[X]) (gamma j a : k) : Prop :=
  (K.eval a = 0 ∧
    ((K.derivative.eval a = 0 ∧
        terminalLoadedFifthKZeroRest68 H b w e D K j a = 0) ∨
      (K.derivative.eval a ≠ 0 ∧
        D.derivative.derivative.derivative.derivative.eval a =
          terminalLoadedFifthKZeroRest68 H b w e D K j a /
            (5 * K.derivative.eval a)))) ∨
  (K.eval a ≠ 0 ∧
    D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a /
        K.eval a ∧
    D.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFifthKNonzeroRest68 H A b w e D K gamma j a /
        K.eval a)

theorem terminalRefinedIIILoadedFifthZeroChildren68_of_rows
    (H A b w e D K : k[X]) (gamma j a : k)
    (hD1 : D.derivative.eval a = 0)
    (hload4 : terminalLoadedFourthSubstitutedResidual68
      H A b w D K gamma j a = 0)
    (hload5 : terminalFifthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFifthPairLeftZeroAt68 D K a =
      60 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.eval a * H.derivative.derivative.eval a ^ 2) :
    terminalRefinedIIILoadedFifthZeroChildren68 H A b w e D K gamma j a := by
  have hD4 := terminalLoadedFourth_controls_D4_68 H A b w D K gamma j a hload4
  by_cases hK : K.eval a = 0
  · left
    refine ⟨hK, ?_⟩
    have hc := terminalLoadedFifth_KZero_controls_D4K1_68
      H b w e D K j a hD1 hK hload5
    by_cases hK1 : K.derivative.eval a = 0
    · left
      refine ⟨hK1, ?_⟩
      rw [hK1, mul_zero] at hc
      exact hc.symm
    · right
      refine ⟨hK1, ?_⟩
      exact (eq_div_iff (mul_ne_zero (by norm_num) hK1)).2 (by
        linear_combination hc)
  · right
    refine ⟨hK, (eq_div_iff hK).2 hD4, ?_⟩
    exact terminalLoadedFifth_KNonzero_controls_D5_68
      H A b w e D K gamma j a hD1 hK hD4 hload5

end LoadedFifthAlgebra68

section LoadedFifthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Full source-facing fifth-loaded split; the nonzero refined-III component
is returned without alteration. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIILoadedFifthSplit
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
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
    terminalRefinedIIILoadedFifthZeroChildren68 H A0 b2 w
        (terminalEDerivativeNumerator68 H E0) D K S.gamma j a ∨
      (D.derivative.eval a ≠ 0 ∧
        phi.derivative.derivative.derivative.eval a ≠ 0) := by
  have hsource := S.terminalRefinedIIIResultantSourcePacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
  dsimp only at hsource
  rcases hsource.1.2.2.2.2.2 with hzero | hnonzero
  · left
    have hload5 := terminalLoadedFifth_of_row_68 H b2 w
      (terminalEDerivativeNumerator68 H E0) D K j a ha hw hw1 hD hrow
    exact terminalRefinedIIILoadedFifthZeroChildren68_of_rows H A0 b2 w
      (terminalEDerivativeNumerator68 H E0) D K S.gamma j a hzero.1
        hsource.2 hload5
  · exact Or.inr hnonzero

end LoadedFifthSource68

end Max11DegreeRoutes
