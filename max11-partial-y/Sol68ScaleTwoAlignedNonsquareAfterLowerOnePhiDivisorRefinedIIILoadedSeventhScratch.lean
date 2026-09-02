import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIKDegreeScratch

/-! # The homogeneous seventh loaded row on the refined-III deep child

At order seven the load `j H^3` vanishes identically because the core has
degree two.  We keep the triple-product side factored as an iterated
derivative and expand only the three surviving terms of `(D*K)^(7)`.
-/

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

section LoadedSeventhAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The unexpanded left triple product at loaded order seven. -/
def terminalSeventhTripleAt68 (b w e : k[X]) (a : k) : k :=
  (derivative^[7] (b * w * e)).eval a

/-- On `D(a)=D'(a)=K(a)=K'(a)=K''(a)=0`, only three terms of
`(D*K)^(7)(a)` survive. -/
def terminalSeventhPairDeepAt68 (D K : k[X]) (a : k) : k :=
  21 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.eval a +
    35 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.eval a +
    35 * D.derivative.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.eval a

theorem eval_seventh_pair_deep_68
    (D K : k[X]) (a : k)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0) :
    (derivative^[7] (D * K)).eval a =
      terminalSeventhPairDeepAt68 D K a := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    terminalSeventhPairDeepAt68,
    derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat, hD0, hD1, hK0, hK1, hK2, zero_mul,
    mul_zero, zero_add, add_zero]
  ring

theorem seventh_derivative_C_mul_H_cube_eq_zero_68
    (H : k[X]) (j : k) (hdeg : H.natDegree = 2) :
    derivative^[7] (C j * H ^ 3) = 0 := by
  have hpow : (H ^ 3).natDegree = 6 := by
    rw [natDegree_pow, hdeg]
  have hbound : (C j * H ^ 3).natDegree < 7 := by
    have hmul : (C j * H ^ 3).natDegree ≤
        (C j).natDegree + (H ^ 3).natDegree := natDegree_mul_le
    have hC : (C j).natDegree = 0 := natDegree_C j
    omega
  have hz := iterate_derivative_eq_zero (p := C j * H ^ 3) hbound
  simpa only [Function.iterate_succ_apply'] using hz

theorem terminalLoadedSeventh_of_row_68
    (H b w e D K : k[X]) (j a : k)
    (hdeg : H.natDegree = 2)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalSeventhTripleAt68 b w e a -
        terminalSeventhPairDeepAt68 D K a = 0 := by
  have h7 := congrArg (fun P : k[X] =>
    (derivative^[7] P).eval a) hrow
  have hload := seventh_derivative_C_mul_H_cube_eq_zero_68 H j hdeg
  rw [hload] at h7
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    derivative_sub, eval_sub,
    terminalSeventhTripleAt68,
    eval_zero] at h7
  have hpair := eval_seventh_pair_deep_68 D K a hD0 hD1 hK0 hK1 hK2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    at hpair
  rw [hpair] at h7
  simpa only [terminalSeventhTripleAt68, Function.iterate_succ_apply',
    Function.iterate_zero_apply] using h7

def terminalLoadedSeventhKTripleZeroRest68
    (b w e D K : k[X]) (a : k) : k :=
  terminalSeventhTripleAt68 b w e a -
    21 * D.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.derivative.eval a -
    35 * D.derivative.derivative.derivative.eval a *
      K.derivative.derivative.derivative.derivative.eval a

theorem terminalLoadedSeventh_KTripleZero_controls_D4K3_68
    (b w e D K : k[X]) (a : k)
    (hload7 : terminalSeventhTripleAt68 b w e a -
      terminalSeventhPairDeepAt68 D K a = 0) :
    35 * D.derivative.derivative.derivative.derivative.eval a *
        K.derivative.derivative.derivative.eval a =
      terminalLoadedSeventhKTripleZeroRest68 b w e D K a := by
  dsimp only [terminalSeventhPairDeepAt68,
    terminalLoadedSeventhKTripleZeroRest68] at hload7 ⊢
  linear_combination -hload7

def terminalRefinedIIILoadedSeventhDeepChildren68
    (H b w e D K : k[X]) (j a : k) : Prop :=
  K.eval a = 0 ∧ K.derivative.eval a = 0 ∧
    K.derivative.derivative.eval a = 0 ∧
    terminalLoadedFifthKZeroRest68 H b w e D K j a = 0 ∧
    terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0 ∧
    ((K.derivative.derivative.derivative.eval a = 0 ∧
        terminalLoadedSeventhKTripleZeroRest68 b w e D K a = 0) ∨
      (K.derivative.derivative.derivative.eval a ≠ 0 ∧
        D.derivative.derivative.derivative.derivative.eval a =
          terminalLoadedSeventhKTripleZeroRest68 b w e D K a /
            (35 * K.derivative.derivative.derivative.eval a)))

def terminalRefinedIIILoadedSixthKTwoSolved68
    (H b w e D K : k[X]) (j a : k) : Prop :=
  K.eval a = 0 ∧ K.derivative.eval a = 0 ∧
    terminalLoadedFifthKZeroRest68 H b w e D K j a = 0 ∧
    K.derivative.derivative.eval a ≠ 0 ∧
    D.derivative.derivative.derivative.derivative.eval a =
      terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a /
        (15 * K.derivative.derivative.eval a)

theorem terminalRefinedIIILoadedSeventhDeepChildren68_of_row
    (H b w e D K : k[X]) (j a : k)
    (hdeg : H.natDegree = 2)
    (hD0 : D.eval a = 0) (hD1 : D.derivative.eval a = 0)
    (hK0 : K.eval a = 0) (hK1 : K.derivative.eval a = 0)
    (hK2 : K.derivative.derivative.eval a = 0)
    (hrest5 : terminalLoadedFifthKZeroRest68 H b w e D K j a = 0)
    (hrest6 : terminalLoadedSixthKDoubleZeroRest68 H b w e D K j a = 0)
    (hrow : b * w * e - D * K = C j * H ^ 3) :
    terminalRefinedIIILoadedSeventhDeepChildren68 H b w e D K j a := by
  refine ⟨hK0, hK1, hK2, hrest5, hrest6, ?_⟩
  have hload7 := terminalLoadedSeventh_of_row_68 H b w e D K j a hdeg
    hD0 hD1 hK0 hK1 hK2 hrow
  have hc := terminalLoadedSeventh_KTripleZero_controls_D4K3_68
    b w e D K a hload7
  by_cases hK3 : K.derivative.derivative.derivative.eval a = 0
  · left
    refine ⟨hK3, ?_⟩
    rw [hK3, mul_zero] at hc
    exact hc.symm
  · right
    refine ⟨hK3, ?_⟩
    exact (eq_div_iff (mul_ne_zero (by norm_num) hK3)).2 (by
      linear_combination hc)

end LoadedSeventhAlgebra68

section LoadedSeventhSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-backed loaded order seven.  All previously solved siblings are
returned verbatim; only the `K=K'=K''=0` child is refined. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIILoadedSeventhSplit
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
    terminalRefinedIIILoadedSeventhDeepChildren68 H b2 w
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
  · have hprev := S.terminalRefinedIIILoadedSixthSplit (H := H)
      A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
        hph1 hph2 hI4 hrow hlower
    rcases hprev with hdeep | hsiblings | hnonzero
    · dsimp only [terminalRefinedIIILoadedSixthDeepChildren68] at hdeep
      rcases hdeep with ⟨hK0, hK1, hrest5, hK2zero | hK2nonzero⟩
      · left
        exact terminalRefinedIIILoadedSeventhDeepChildren68_of_row H b2 w
          (terminalEDerivativeNumerator68 H E0) D K j a hdeg hD
          hDzero.1
          hK0 hK1 hK2zero.1 hrest5 hK2zero.2 hrow
      · right; left
        exact ⟨hK0, hK1, hrest5, hK2nonzero.1, hK2nonzero.2⟩
    · right; right; left
      exact hsiblings
    · exact (hnonzero.1 hDzero.1).elim
  · right; right; right
    exact hDnonzero

end LoadedSeventhSource68

end Max11DegreeRoutes
