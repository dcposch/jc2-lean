import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedFifthScratch

/-! # The sixth loaded row on the `K = K' = 0` child -/

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

section LoadedSixthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalSixthTripleMiddleDoubleZeroAt68
    (b w e : k[X]) (a : k) : k :=
  15 * b.derivative.derivative.derivative.derivative.eval a *
      w.derivative.derivative.eval a * e.eval a +
    20 * b.derivative.derivative.derivative.eval a *
      w.derivative.derivative.derivative.eval a * e.eval a +
    15 * b.derivative.derivative.eval a *
      w.derivative.derivative.derivative.derivative.eval a * e.eval a +
    6 * b.derivative.eval a *
      w.derivative.derivative.derivative.derivative.derivative.eval a * e.eval a +
    b.eval a *
      w.derivative.derivative.derivative.derivative.derivative.derivative.eval a *
      e.eval a +
    60 * b.derivative.derivative.derivative.eval a *
      w.derivative.derivative.eval a * e.derivative.eval a +
    60 * b.derivative.derivative.eval a *
      w.derivative.derivative.derivative.eval a * e.derivative.eval a +
    30 * b.derivative.eval a *
      w.derivative.derivative.derivative.derivative.eval a * e.derivative.eval a +
    6 * b.eval a *
      w.derivative.derivative.derivative.derivative.derivative.eval a *
      e.derivative.eval a +
    90 * b.derivative.derivative.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.eval a +
    60 * b.derivative.eval a * w.derivative.derivative.derivative.eval a *
      e.derivative.derivative.eval a +
    15 * b.eval a * w.derivative.derivative.derivative.derivative.eval a *
      e.derivative.derivative.eval a +
    60 * b.derivative.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.derivative.eval a +
    20 * b.eval a * w.derivative.derivative.derivative.eval a *
      e.derivative.derivative.derivative.eval a +
    15 * b.eval a * w.derivative.derivative.eval a *
      e.derivative.derivative.derivative.derivative.eval a

def terminalSixthPairLeftZeroAt68 (D K : k[X]) (a : k) : k :=
  D.derivative.derivative.derivative.derivative.derivative.derivative.eval a *
      K.eval a +
    6 * D.derivative.derivative.derivative.derivative.derivative.eval a *
      K.derivative.eval a +
    15 * D.derivative.derivative.derivative.derivative.eval a *
      K.derivative.derivative.eval a +
    20 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a +
    15 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.eval a +
    6 * D.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.eval a

theorem eval_sixth_triple_middle_double_zero_68
    (b w e : k[X]) (a : k) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) :
    (b * w * e).derivative.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalSixthTripleMiddleDoubleZeroAt68 b w e a := by
  simp only [terminalSixthTripleMiddleDoubleZeroAt68, derivative_add,
    derivative_mul, eval_add, eval_mul, eval_ofNat, hw, hw1, zero_mul,
    mul_zero, zero_add, add_zero]
  ring

theorem eval_sixth_pair_left_zero_68
    (D K : k[X]) (a : k) (hD : D.eval a = 0) :
    (D * K).derivative.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalSixthPairLeftZeroAt68 D K a := by
  simp only [terminalSixthPairLeftZeroAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat, hD, zero_mul, add_zero]
  ring

theorem eval_sixth_C_mul_cube_at_root_68
    (H : k[X]) (j a : k) (ha : H.eval a = 0) :
    (C j * H ^ 3).derivative.derivative.derivative.derivative.derivative.derivative.eval a =
      90 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.derivative.eval a +
        360 * j * H.derivative.eval a * H.derivative.derivative.eval a *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.derivative.eval a ^ 3 := by
  simp [derivative_mul, derivative_pow, ha]
  ring

theorem terminalLoadedSixth_of_row_68
    (H b w e D K : k[X]) (j a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0)
    (hw1 : w.derivative.eval a = 0) (hD : D.eval a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalSixthTripleMiddleDoubleZeroAt68 b w e a -
        terminalSixthPairLeftZeroAt68 D K a =
      90 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.derivative.eval a +
        360 * j * H.derivative.eval a * H.derivative.derivative.eval a *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.derivative.eval a ^ 3 := by
  have h6 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.derivative.eval a)
      hrow
  simp only [derivative_sub, eval_sub,
    eval_sixth_triple_middle_double_zero_68 b w e a hw hw1,
    eval_sixth_pair_left_zero_68 D K a hD,
    eval_sixth_C_mul_cube_at_root_68 H j a ha] at h6
  exact h6

def terminalLoadedSixthKDoubleZeroRest68
    (H b w e D K : k[X]) (j a : k) : k :=
  terminalSixthTripleMiddleDoubleZeroAt68 b w e a -
    20 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a -
    15 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.eval a -
    (90 * j * H.derivative.eval a ^ 2 *
        H.derivative.derivative.derivative.derivative.eval a +
      360 * j * H.derivative.eval a * H.derivative.derivative.eval a *
        H.derivative.derivative.derivative.eval a +
      90 * j * H.derivative.derivative.eval a ^ 3)

theorem terminalLoadedSixth_KDoubleZero_controls_D4K2_68
    (H b w e D K : k[X]) (j a : k)
    (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hload6 : terminalSixthTripleMiddleDoubleZeroAt68 b w e a -
        terminalSixthPairLeftZeroAt68 D K a =
      90 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.derivative.eval a +
        360 * j * H.derivative.eval a * H.derivative.derivative.eval a *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.derivative.eval a ^ 3) :
    15 * D.derivative.derivative.derivative.derivative.eval a *
        K.derivative.derivative.eval a =
      terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a := by
  dsimp only [terminalSixthPairLeftZeroAt68,
    terminalLoadedSixthKDoubleZeroRest68] at hload6 ⊢
  simp only [hD1, hK0, hK1, mul_zero, zero_mul, add_zero] at hload6
  linear_combination -hload6

def terminalRefinedIIILoadedSixthDeepChildren68
    (H b w e D K : k[X]) (j a : k) : Prop :=
  K.eval a = 0 ∧ K.derivative.eval a = 0 ∧
    terminalLoadedFifthKZeroRest68 H b w e D K j a = 0 ∧
    ((K.derivative.derivative.eval a = 0 ∧
        terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0) ∨
      (K.derivative.derivative.eval a ≠ 0 ∧
        D.derivative.derivative.derivative.derivative.eval a =
          terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a /
            (15 * K.derivative.derivative.eval a)))

def terminalRefinedIIILoadedFifthSolvedSiblings68
    (H A b w e D K : k[X]) (gamma j a : k) : Prop :=
  (K.eval a = 0 ∧ K.derivative.eval a ≠ 0 ∧
    D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFifthKZeroRest68 H b w e D K j a /
        (5 * K.derivative.eval a)) ∨
  (K.eval a ≠ 0 ∧
    D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a /
        K.eval a ∧
    D.derivative.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedFifthKNonzeroRest68 H A b w e D K gamma j a /
        K.eval a)

theorem terminalRefinedIIILoadedSixthDeepChildren68_of_row
    (H b w e D K : k[X]) (j a : k)
    (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hrest5 : terminalLoadedFifthKZeroRest68 H b w e D K j a = 0)
    (hload6 : terminalSixthTripleMiddleDoubleZeroAt68 b w e a -
        terminalSixthPairLeftZeroAt68 D K a =
      90 * j * H.derivative.eval a ^ 2 *
          H.derivative.derivative.derivative.derivative.eval a +
        360 * j * H.derivative.eval a * H.derivative.derivative.eval a *
          H.derivative.derivative.derivative.eval a +
        90 * j * H.derivative.derivative.eval a ^ 3) :
    terminalRefinedIIILoadedSixthDeepChildren68 H b w e D K j a := by
  refine ⟨hK0, hK1, hrest5, ?_⟩
  have hc := terminalLoadedSixth_KDoubleZero_controls_D4K2_68
    H b w e D K j a hD1 hK0 hK1 hload6
  by_cases hK2 : K.derivative.derivative.eval a = 0
  · left
    refine ⟨hK2, ?_⟩
    rw [hK2, mul_zero] at hc
    exact hc.symm
  · right
    refine ⟨hK2, ?_⟩
    exact (eq_div_iff (mul_ne_zero (by norm_num) hK2)).2 (by
      linear_combination hc)

end LoadedSixthAlgebra68

section LoadedSixthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIILoadedSixthSplit
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
    terminalRefinedIIILoadedSixthDeepChildren68 H b2 w
        (terminalEDerivativeNumerator68 H E0) D K j a ∨
      terminalRefinedIIILoadedFifthSolvedSiblings68 H A0 b2 w
        (terminalEDerivativeNumerator68 H E0) D K S.gamma j a ∨
      (D.derivative.eval a ≠ 0 ∧
        phi.derivative.derivative.derivative.eval a ≠ 0) := by
  have hresult := S.terminalRefinedIIIResultantSourcePacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
  dsimp only at hresult
  rcases hresult.1.2.2.2.2.2 with hDzero | hDnonzero
  · have hprev := S.terminalRefinedIIILoadedFifthSplit (H := H)
      A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
        hph1 hph2 hI4 hrow hlower
    rcases hprev with hzero | hnonzero
    · dsimp only [terminalRefinedIIILoadedFifthZeroChildren68] at hzero
      rcases hzero with hKzero | hKnonzero
      · rcases hKzero with ⟨hK0, hK1zero | hK1nonzero⟩
        · left
          have hload6 := terminalLoadedSixth_of_row_68 H b2 w
            (terminalEDerivativeNumerator68 H E0) D K j a ha hw hw1 hD hrow
          exact terminalRefinedIIILoadedSixthDeepChildren68_of_row H b2 w
            (terminalEDerivativeNumerator68 H E0) D K j a hDzero.1
              hK0 hK1zero.1 hK1zero.2 hload6
        · right; left; left
          exact ⟨hK0, hK1nonzero.1, hK1nonzero.2⟩
      · right; left; right
        exact hKnonzero
    · exact (hnonzero.1 hDzero.1).elim
  · exact Or.inr (Or.inr hDnonzero)

end LoadedSixthSource68

end Max11DegreeRoutes
