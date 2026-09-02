import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIResultantSourceScratch

/-! # The zero component of the refined-III resultant -/

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

section ZeroComponentAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Remove the unique `D'''' * K` term from the loaded fourth residual. -/
def terminalLoadedFourthZeroBranchRest68
    (H A b w D K : k[X]) (gamma j a : k) : k :=
  terminalLoadedFourthSubstitutedResidual68 H A b w D K gamma j a +
    D.derivative.derivative.derivative.derivative.eval a * K.eval a

theorem terminalLoadedFourth_controls_D4_68
    (H A b w D K : k[X]) (gamma j a : k)
    (hload : terminalLoadedFourthSubstitutedResidual68
      H A b w D K gamma j a = 0) :
    D.derivative.derivative.derivative.derivative.eval a * K.eval a =
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a := by
  dsimp only [terminalLoadedFourthZeroBranchRest68]
  linear_combination -hload

theorem terminalLoadedFourth_D4_componentSplit_68
    (H A b w D K : k[X]) (gamma j a : k)
    (hload : terminalLoadedFourthSubstitutedResidual68
      H A b w D K gamma j a = 0) :
    (K.eval a = 0 ∧
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a = 0) ∨
    (K.eval a ≠ 0 ∧
      D.derivative.derivative.derivative.derivative.eval a =
        terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a /
          K.eval a) := by
  have hc := terminalLoadedFourth_controls_D4_68 H A b w D K gamma j a hload
  by_cases hK : K.eval a = 0
  · left
    refine ⟨hK, ?_⟩
    rw [hK, mul_zero] at hc
    exact hc.symm
  · right
    exact ⟨hK, (eq_div_iff hK).2 hc⟩

theorem terminalLoadedFourth_D4_productSplit_68
    (H A b w D K : k[X]) (gamma j a : k)
    (hload : terminalLoadedFourthSubstitutedResidual68
      H A b w D K gamma j a = 0) :
    (K.eval a = 0 ∧
      terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a = 0) ∨
    (K.eval a ≠ 0 ∧
      D.derivative.derivative.derivative.derivative.eval a * K.eval a =
        terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a) := by
  have hc := terminalLoadedFourth_controls_D4_68 H A b w D K gamma j a hload
  by_cases hK : K.eval a = 0
  · left
    refine ⟨hK, ?_⟩
    rw [hK, mul_zero] at hc
    exact hc.symm
  · exact Or.inr ⟨hK, hc⟩

end ZeroComponentAlgebra68

section ZeroComponentSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

def terminalRefinedIIIZeroComponentSourceData68
    (H A b D phi w K : k[X]) (gamma j a : k) : Prop :=
  let L := 16 * A.eval a * b.eval a ^ 2 * H.derivative.eval a *
        H.derivative.derivative.eval a +
      32 * A.eval a * b.eval a * b.derivative.eval a *
        H.derivative.eval a ^ 2 -
      16 * A.derivative.eval a * b.eval a ^ 2 * H.derivative.eval a ^ 2
  let N := -3 * H.derivative.eval a * A.eval a ^ 3 *
        b.derivative.eval a * w.derivative.derivative.eval a -
      6 * H.derivative.eval a * A.eval a ^ 2 * A.derivative.eval a *
        b.eval a * w.derivative.derivative.eval a -
      3 * H.derivative.derivative.eval a * A.eval a ^ 3 * b.eval a *
        w.derivative.derivative.eval a -
      9 * (D.derivative.derivative.derivative.eval a * K.eval a +
        3 * D.derivative.derivative.eval a * K.derivative.eval a) -
      54 * j * H.derivative.eval a ^ 3
  let m := b.eval a * phi.derivative.derivative.derivative.derivative.eval a
  let m5 := 5 * b.derivative.eval a *
        phi.derivative.derivative.derivative.derivative.eval a +
      b.eval a * phi.derivative.derivative.derivative.derivative.derivative.eval a +
      60 * w.derivative.derivative.eval a * D.derivative.derivative.derivative.eval a
  let f5 := -6 * A.eval a ^ 2 * w.derivative.derivative.derivative.eval a + L
  f5 = 0 ∧
    36 * w.derivative.derivative.eval a * D.derivative.derivative.eval a + m = 0 ∧
    36 * w.derivative.derivative.eval a * m5 -
      60 * w.derivative.derivative.derivative.eval a * m = 0 ∧
    6 * A.eval a ^ 2 * N -
      (H.derivative.eval a * A.eval a ^ 3 * b.eval a) * L = 0 ∧
    ((K.eval a = 0 ∧
        terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a = 0) ∨
      (K.eval a ≠ 0 ∧
        D.derivative.derivative.derivative.derivative.eval a * K.eval a =
          terminalLoadedFourthZeroBranchRest68 H A b w D K gamma j a))

/-- The source resultant specializes either to a rigid zero-component packet
or leaves the nonzero component literally unchanged. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIZeroComponentSplit
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
    terminalRefinedIIIZeroComponentSourceData68
      H A0 b2 D phi w K S.gamma j a ∨
    (D.derivative.eval a ≠ 0 ∧
      phi.derivative.derivative.derivative.eval a ≠ 0) := by
  have hsource := S.terminalRefinedIIIResultantSourcePacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
  dsimp only at hsource
  dsimp only [terminalRefinedIIIZeroComponentSourceData68]
  let u := -(5 / 3 : k) * A0.eval a ^ 2 * b2.eval a * H.derivative.eval a
  let v := 78 * A0.eval a * H.derivative.eval a *
      w.derivative.derivative.eval a -
    (160 / 9 : k) * b2.eval a ^ 2 * H.derivative.eval a ^ 3
  let n := terminalLowerZeroSixthRest68 H A0 b2 D phi w S.gamma a
  let m0 := 4 * b2.derivative.eval a *
        phi.derivative.derivative.derivative.eval a +
      b2.eval a * phi.derivative.derivative.derivative.derivative.eval a +
      24 * w.derivative.derivative.derivative.eval a * D.derivative.eval a
  let m50 := 10 * b2.derivative.derivative.eval a *
        phi.derivative.derivative.derivative.eval a +
      5 * b2.derivative.eval a *
        phi.derivative.derivative.derivative.derivative.eval a +
      b2.eval a *
        phi.derivative.derivative.derivative.derivative.derivative.eval a +
      60 * w.derivative.derivative.eval a * D.derivative.derivative.derivative.eval a
  have hpacket : terminalRefinedIIISixthResultantPacket68 u v n
      (w.derivative.derivative.eval a) m0 (D.derivative.eval a)
      (w.derivative.derivative.derivative.eval a) m50
      (w.derivative.derivative.derivative.derivative.eval a)
      (D.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.eval a) (b2.eval a) := by
    simpa only [u, v, n, m0, m50] using hsource.1
  rcases hpacket.2.2.2.2.2 with hzero | hnonzero
  · left
    rcases hzero with ⟨hd1, hp3⟩
    have hload3 := congrArg (fun P : k[X] =>
      P.derivative.derivative.derivative.eval a) hrow
    simp only [derivative_sub, eval_sub] at hload3
    rw [terminalThirdTripleAt68_eq, terminalThirdPairAt68_eq,
      terminalThirdCoreLoad68_eq H j a ha,
      terminalThirdTripleAt68_of_middle_zero b2 w
        (terminalEDerivativeNumerator68 H E0) a hw,
      terminalThirdTripleMiddleZeroAt68_of_derivative_zero b2 w
        (terminalEDerivativeNumerator68 H E0) a hw1,
      terminalThirdPairAt68_of_left_zero D K a hD] at hload3
    have hprev := S.terminalRefinedIIIFifthLocalPacket (H := H)
      A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
        hph1 hph2 hI4 hload3 hlower
    have hnext := S.terminalRefinedIIILoadedNextPacket (H := H)
      A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
        hph1 hph2 hI4 hrow hlower
    let L := 16 * A0.eval a * b2.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A0.eval a * b2.eval a * b2.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A0.derivative.eval a * b2.eval a ^ 2 * H.derivative.eval a ^ 2
    let N := -3 * H.derivative.eval a * A0.eval a ^ 3 *
          b2.derivative.eval a * w.derivative.derivative.eval a -
        6 * H.derivative.eval a * A0.eval a ^ 2 * A0.derivative.eval a *
          b2.eval a * w.derivative.derivative.eval a -
        3 * H.derivative.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.eval a -
        9 * (D.derivative.derivative.derivative.eval a * K.eval a +
          3 * D.derivative.derivative.eval a * K.derivative.eval a) -
        54 * j * H.derivative.eval a ^ 3
    let m := b2.eval a * phi.derivative.derivative.derivative.derivative.eval a
    let m5 := 5 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.derivative.eval a +
        b2.eval a *
          phi.derivative.derivative.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.eval a * D.derivative.derivative.derivative.eval a
    have hfive : -6 * A0.eval a ^ 2 *
        w.derivative.derivative.derivative.eval a + L = 0 := by
      dsimp only [L]
      have hf := hprev.2.2.2.2.1
      rw [hd1, mul_zero, zero_mul, add_zero] at hf
      linear_combination hf
    have hfour : 36 * w.derivative.derivative.eval a *
        D.derivative.derivative.eval a + m = 0 := by
      have hf := hpacket.2.2.1
      dsimp only [m0] at hf
      simp only [hp3, hd1, mul_zero, zero_mul, zero_add, add_zero] at hf
      dsimp only [m]
      linear_combination hf
    have hres : 36 * w.derivative.derivative.eval a * m5 -
        60 * w.derivative.derivative.derivative.eval a * m = 0 := by
      have hr := hpacket.2.2.2.2.1
      dsimp only [u, v, n, m0, m50] at hr
      simp only [hd1, hp3, mul_zero, zero_mul, zero_add, add_zero] at hr
      have hc : -(36 * w.derivative.derivative.eval a *
          (-(5 / 3 : k) * A0.eval a ^ 2 * b2.eval a *
            H.derivative.eval a)) ≠ 0 := by
        exact neg_ne_zero.mpr (mul_ne_zero
          (mul_ne_zero (by norm_num) hpacket.2.1) hpacket.1)
      have hfac : -(36 * w.derivative.derivative.eval a *
          (-(5 / 3 : k) * A0.eval a ^ 2 * b2.eval a *
            H.derivative.eval a)) *
          (36 * w.derivative.derivative.eval a * m5 -
            60 * w.derivative.derivative.derivative.eval a * m) = 0 := by
        dsimp only [m, m5]
        linear_combination hr
      exact (mul_eq_zero.mp hfac).resolve_left hc
    have hloadElim := hnext.2.2.2.1
    have hloadSimple : 6 * A0.eval a ^ 2 * N -
        (H.derivative.eval a * A0.eval a ^ 3 * b2.eval a) * L = 0 := by
      dsimp only [L, N] at hloadElim ⊢
      simp only [hp3, mul_zero, zero_mul, zero_add, add_zero] at hloadElim
      have hfac : 9 * w.derivative.derivative.eval a *
          (6 * A0.eval a ^ 2 * N -
            (H.derivative.eval a * A0.eval a ^ 3 * b2.eval a) * L) = 0 := by
        dsimp only [L, N]
        linear_combination hloadElim
      have hc : 9 * w.derivative.derivative.eval a ≠ 0 :=
        mul_ne_zero (by norm_num) hpacket.2.1
      exact (mul_eq_zero.mp hfac).resolve_left hc
    exact ⟨hfive, hfour, hres, hloadSimple,
      terminalLoadedFourth_D4_productSplit_68 H A0 b2 w D K S.gamma j a
        hsource.2⟩
  · exact Or.inr hnonzero

end ZeroComponentSource68

end Max11DegreeRoutes
