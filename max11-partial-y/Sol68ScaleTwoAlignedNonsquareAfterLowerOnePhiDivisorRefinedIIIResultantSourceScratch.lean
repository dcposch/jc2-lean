import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIISixthScratch

/-! # Source instantiation of the refined-III sixth resultant -/

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

section ResultantAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The part of the sixth face not containing `w''''` or `D''`. -/
def terminalLowerZeroSixthRest68
    (H A B D phi w : k[X]) (gamma a : k) : k :=
  terminalLowerZeroSixthFace68 H A B D phi w gamma a -
    (-(5 / 3 : k) * A.eval a ^ 2 * B.eval a * H.derivative.eval a) *
      w.derivative.derivative.derivative.derivative.eval a -
    (78 * A.eval a * H.derivative.eval a * w.derivative.derivative.eval a -
      (160 / 9 : k) * B.eval a ^ 2 * H.derivative.eval a ^ 3) *
      D.derivative.derivative.eval a

theorem terminalLowerZeroSixthFace_decomposition_68
    (H A B D phi w : k[X]) (gamma a : k) :
    let u := -(5 / 3 : k) * A.eval a ^ 2 * B.eval a * H.derivative.eval a
    let v := 78 * A.eval a * H.derivative.eval a *
        w.derivative.derivative.eval a -
      (160 / 9 : k) * B.eval a ^ 2 * H.derivative.eval a ^ 3
    terminalLowerZeroSixthFace68 H A B D phi w gamma a =
      u * w.derivative.derivative.derivative.derivative.eval a +
        v * D.derivative.derivative.eval a +
        terminalLowerZeroSixthRest68 H A B D phi w gamma a := by
  dsimp only [terminalLowerZeroSixthRest68]
  ring

def terminalRefinedIIISixthResultantPacket68
    (u v n W m d1 w3 m5 x y P b : k) : Prop :=
  u ≠ 0 ∧ W ≠ 0 ∧
    36 * W * y + m = 0 ∧
    36 * W * u * x + 36 * W * n - v * m = 0 ∧
    1080 * W * d1 * (36 * W * n - v * m) -
      36 * W * u * (36 * W * m5 - 60 * w3 * m) = 0 ∧
    ((d1 = 0 ∧ P = 0) ∨ (d1 ≠ 0 ∧ P ≠ 0))

theorem terminalRefinedIIISixthResultantPacket68_of_faces
    (u v n W m d1 w3 m5 x y P b : k)
    (hu : u ≠ 0) (hW : W ≠ 0) (hb : b ≠ 0)
    (hthird : b * P + 18 * W * d1 = 0)
    (h6 : u * x + v * y + n = 0)
    (h4 : 36 * W * y + m = 0)
    (h5 : 30 * d1 * x + 60 * w3 * y + m5 = 0) :
    terminalRefinedIIISixthResultantPacket68
      u v n W m d1 w3 m5 x y P b := by
  have hx : 36 * W * u * x + 36 * W * n - v * m = 0 := by
    linear_combination 36 * W * h6 - v * h4
  have hres := terminalRefinedIII_sixth_I4_resultant_68
    u v n W m d1 w3 m5 x y h6 h4 h5
  refine ⟨hu, hW, h4, hx, hres, ?_⟩
  by_cases hd : d1 = 0
  · left
    refine ⟨hd, ?_⟩
    rw [hd, mul_zero, add_zero] at hthird
    exact (mul_eq_zero.mp hthird).resolve_left hb
  · right
    refine ⟨hd, ?_⟩
    intro hp
    rw [hp, mul_zero, zero_add] at hthird
    have hc : 18 * W ≠ 0 := mul_ne_zero (by norm_num) hW
    exact hd ((mul_eq_zero.mp hthird).resolve_left hc)

/-- A short form of the fully substituted fourth loaded relation. -/
def terminalLoadedFourthSubstitutedResidual68
    (H A b w d K : k[X]) (gamma j a : k) : k :=
  let e0 := -(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3
  let e1 := -(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
      A.derivative.eval a -
    (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3
  let e2 := -(2 / 9 : k) * H.derivative.eval a * A.eval a *
        A.derivative.eval a ^ 2 -
      (1 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
        A.derivative.derivative.eval a -
      (5 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 2 *
        A.derivative.eval a -
      (1 / 9 : k) * H.derivative.derivative.derivative.eval a *
        A.eval a ^ 3 + gamma * A.eval a * H.derivative.eval a ^ 3
  6 * b.derivative.derivative.eval a * w.derivative.derivative.eval a * e0 +
    4 * b.derivative.eval a * w.derivative.derivative.derivative.eval a * e0 +
    b.eval a * w.derivative.derivative.derivative.derivative.eval a * e0 +
    12 * b.derivative.eval a * w.derivative.derivative.eval a * e1 +
    4 * b.eval a * w.derivative.derivative.derivative.eval a * e1 +
    6 * b.eval a * w.derivative.derivative.eval a * e2 -
    terminalFourthPairLeftZeroAt68 d K a -
    36 * j * H.derivative.eval a ^ 2 * H.derivative.derivative.eval a

theorem terminalLoadedFourthSubstitutedResidual68_zero
    (H A b w phi d e K : k[X]) (gamma j a : k)
    (he0 : e.eval a = -(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3)
    (he1 : e.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3)
    (he2 : e.derivative.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A.eval a *
          A.derivative.eval a ^ 2 -
        (1 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.derivative.eval a -
        (5 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.derivative.eval a *
          A.eval a ^ 3 + gamma * A.eval a * H.derivative.eval a ^ 3)
    (hload4 : terminalFourthTripleMiddleDoubleZeroAt68 b w e a -
        terminalFourthPairLeftZeroAt68 d K a =
      36 * j * H.derivative.eval a ^ 2 * H.derivative.derivative.eval a) :
    terminalLoadedFourthSubstitutedResidual68 H A b w d K gamma j a = 0 := by
  have hs := terminalLoadedFourth_substituted_68 H A b w phi d e K gamma j a
    he0 he1 he2 hload4
  dsimp only at hs
  dsimp only [terminalLoadedFourthSubstitutedResidual68]
  linear_combination hs

end ResultantAlgebra68

section ResultantSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Exact source instantiation of the sixth resultant.  The last two fields
retain the substituted loaded row and both earlier elimination polynomials. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIResultantSourcePacket
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
    let u := -(5 / 3 : k) * A0.eval a ^ 2 * b2.eval a * H.derivative.eval a
    let v := 78 * A0.eval a * H.derivative.eval a *
        w.derivative.derivative.eval a -
      (160 / 9 : k) * b2.eval a ^ 2 * H.derivative.eval a ^ 3
    let n := terminalLowerZeroSixthRest68 H A0 b2 D phi w S.gamma a
    let m := 4 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        b2.eval a * phi.derivative.derivative.derivative.derivative.eval a +
        24 * w.derivative.derivative.derivative.eval a * D.derivative.eval a
    let m5 := 10 * b2.derivative.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        5 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.derivative.eval a +
        b2.eval a *
          phi.derivative.derivative.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.eval a *
          D.derivative.derivative.derivative.eval a
    terminalRefinedIIISixthResultantPacket68 u v n
      (w.derivative.derivative.eval a) m (D.derivative.eval a)
      (w.derivative.derivative.derivative.eval a) m5
      (w.derivative.derivative.derivative.derivative.eval a)
      (D.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.eval a) (b2.eval a) ∧
    terminalLoadedFourthSubstitutedResidual68 H A0 b2 w D K S.gamma j a = 0 := by
  dsimp only
  have hnext := S.terminalRefinedIIILoadedNextPacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
  have hsix := S.terminalRefinedIIISixthLocalPacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hI4 hrow hlower
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
  let u := -(5 / 3 : k) * A0.eval a ^ 2 * b2.eval a * H.derivative.eval a
  let v := 78 * A0.eval a * H.derivative.eval a *
      w.derivative.derivative.eval a -
    (160 / 9 : k) * b2.eval a ^ 2 * H.derivative.eval a ^ 3
  let n := terminalLowerZeroSixthRest68 H A0 b2 D phi w S.gamma a
  let m := 4 * b2.derivative.eval a *
        phi.derivative.derivative.derivative.eval a +
      b2.eval a * phi.derivative.derivative.derivative.derivative.eval a +
      24 * w.derivative.derivative.derivative.eval a * D.derivative.eval a
  let m5 := 10 * b2.derivative.derivative.eval a *
        phi.derivative.derivative.derivative.eval a +
      5 * b2.derivative.eval a *
        phi.derivative.derivative.derivative.derivative.eval a +
      b2.eval a *
        phi.derivative.derivative.derivative.derivative.derivative.eval a +
      60 * w.derivative.derivative.eval a * D.derivative.derivative.derivative.eval a
  have hu : u ≠ 0 := by
    dsimp only [u]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)) hB) hh
  have hW2 : w.derivative.derivative.eval a ≠ 0 := by
    intro hz
    have hfourth := hprev.2.2.1
    rw [hz, mul_zero] at hfourth
    have hr : (8 / 9 : k) * b2.eval a ^ 2 * H.derivative.eval a ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hB))
        (pow_ne_zero 2 hh)
    exact hr hfourth.symm
  have hthird := terminalI4_third_refinedIII_68 b2 D w phi a hw hph hD hw1
    hph1 hph2 hI4
  have hfour := terminalI4_fourth_refinedIII_68 b2 D w phi a hw hph hD hw1
    hph1 hph2 hI4
  have hfaceDecomp := terminalLowerZeroSixthFace_decomposition_68
    H A0 b2 D phi w S.gamma a
  have h6 : u * w.derivative.derivative.derivative.derivative.eval a +
      v * D.derivative.derivative.eval a + n = 0 := by
    dsimp only [u, v, n]
    rw [← hfaceDecomp]
    exact hsix.1
  have h4 : 36 * w.derivative.derivative.eval a *
      D.derivative.derivative.eval a + m = 0 := by
    dsimp only [m]
    linear_combination hfour
  have h5 : 30 * D.derivative.eval a *
        w.derivative.derivative.derivative.derivative.eval a +
      60 * w.derivative.derivative.derivative.eval a *
        D.derivative.derivative.eval a + m5 = 0 := by
    dsimp only [m5]
    linear_combination hsix.2
  have hpacket := terminalRefinedIIISixthResultantPacket68_of_faces
    u v n (w.derivative.derivative.eval a) m (D.derivative.eval a)
      (w.derivative.derivative.derivative.eval a) m5
      (w.derivative.derivative.derivative.derivative.eval a)
      (D.derivative.derivative.eval a)
      (phi.derivative.derivative.derivative.eval a) (b2.eval a)
      hu hW2 hB hthird h6 h4 h5
  have hloaded := terminalLoadedFourthSubstitutedResidual68_zero
    H A0 b2 w phi D (terminalEDerivativeNumerator68 H E0) K S.gamma j a
      hprev.1 hprev.2.1 hnext.1 hnext.2.1
  exact ⟨hpacket, hloaded⟩

end ResultantSource68

end Max11DegreeRoutes
