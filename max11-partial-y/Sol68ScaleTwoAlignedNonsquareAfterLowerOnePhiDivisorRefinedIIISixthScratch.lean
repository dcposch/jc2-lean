import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedNextScratch

/-! # Sixth lower-zero and fifth I4 faces on refined component III -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section RefinedIIISixthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The loaded fourth row after substituting all three source-determined
`eDot` jets. -/
theorem terminalLoadedFourth_substituted_68
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
    let e2 := -(2 / 9 : k) * H.derivative.eval a * A.eval a *
          A.derivative.eval a ^ 2 -
        (1 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
          A.derivative.derivative.eval a -
        (5 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 2 *
          A.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.derivative.eval a *
          A.eval a ^ 3 + gamma * A.eval a * H.derivative.eval a ^ 3
    6 * b.derivative.derivative.eval a * w.derivative.derivative.eval a *
          (-(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3) +
        4 * b.derivative.eval a * w.derivative.derivative.derivative.eval a *
          (-(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3) +
        b.eval a * w.derivative.derivative.derivative.derivative.eval a *
          (-(1 / 9 : k) * H.derivative.eval a * A.eval a ^ 3) +
        12 * b.derivative.eval a * w.derivative.derivative.eval a *
          (-(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
              A.derivative.eval a -
            (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3) +
        4 * b.eval a * w.derivative.derivative.derivative.eval a *
          (-(2 / 9 : k) * H.derivative.eval a * A.eval a ^ 2 *
              A.derivative.eval a -
            (1 / 9 : k) * H.derivative.derivative.eval a * A.eval a ^ 3) +
        6 * b.eval a * w.derivative.derivative.eval a * e2 -
        terminalFourthPairLeftZeroAt68 d K a =
      36 * j * H.derivative.eval a ^ 2 * H.derivative.derivative.eval a := by
  dsimp only
  dsimp only [terminalFourthTripleMiddleDoubleZeroAt68] at hload4
  rw [he0, he1, he2] at hload4
  exact hload4

/-- The next sparse I4 jet. -/
theorem terminalI4_fifth_refinedIII_68
    (b d w phi : k[X]) (a : k)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : d.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hI4 : b * phi + C 6 * w * d = 0) :
    10 * b.derivative.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        5 * b.derivative.eval a *
          phi.derivative.derivative.derivative.derivative.eval a +
        b.eval a *
          phi.derivative.derivative.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.eval a *
          d.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.derivative.eval a *
          d.derivative.derivative.eval a +
        30 * w.derivative.derivative.derivative.derivative.eval a *
          d.derivative.eval a = 0 := by
  have h5 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_ofNat, eval_zero, hw, hphi, hd, hw1,
    hphi1, hphi2, zero_mul, mul_zero, zero_add, add_zero] at h5
  ring_nf at h5 ⊢
  exact h5

/-- Literal fourth jet of the reduced lower-zero polynomial. -/
def terminalLowerZeroSixthFace68
    (H A B D phi w : k[X]) (gamma a : k) : k :=
  -(5 / 3 : k) * A.eval a ^ 2 * B.eval a * H.derivative.eval a *
      w.derivative.derivative.derivative.derivative.eval a +
    (10 / 3 : k) * A.eval a ^ 2 * B.eval a *
      H.derivative.derivative.derivative.eval a * w.derivative.derivative.eval a -
    (20 / 3 : k) * A.eval a ^ 2 * B.derivative.eval a *
      H.derivative.eval a * w.derivative.derivative.derivative.eval a -
    10 * A.eval a ^ 2 * B.derivative.derivative.eval a *
      H.derivative.eval a * w.derivative.derivative.eval a -
    (40 / 3 : k) * A.eval a * A.derivative.eval a * B.eval a *
      H.derivative.eval a * w.derivative.derivative.derivative.eval a -
    40 * A.eval a * A.derivative.eval a * B.derivative.eval a *
      H.derivative.eval a * w.derivative.derivative.eval a -
    20 * A.eval a * A.derivative.derivative.eval a * B.eval a *
      H.derivative.eval a * w.derivative.derivative.eval a +
    (80 / 27 : k) * A.eval a * B.eval a ^ 3 *
      H.derivative.eval a ^ 2 * H.derivative.derivative.derivative.eval a +
    (40 / 9 : k) * A.eval a * B.eval a ^ 3 * H.derivative.eval a *
      H.derivative.derivative.eval a ^ 2 +
    (160 / 3 : k) * A.eval a * B.eval a ^ 2 * B.derivative.eval a *
      H.derivative.eval a ^ 2 * H.derivative.derivative.eval a +
    (80 / 3 : k) * A.eval a * B.eval a ^ 2 *
      B.derivative.derivative.eval a * H.derivative.eval a ^ 3 +
    (160 / 3 : k) * A.eval a * B.eval a * B.derivative.eval a ^ 2 *
      H.derivative.eval a ^ 3 +
    (1 / 2 : k) * A.eval a * B.eval a * H.derivative.eval a *
      phi.derivative.derivative.derivative.derivative.eval a +
    2 * A.eval a * B.eval a * H.derivative.derivative.eval a *
      phi.derivative.derivative.derivative.eval a +
    2 * A.eval a * B.derivative.eval a * H.derivative.eval a *
      phi.derivative.derivative.derivative.eval a +
    52 * A.eval a * D.derivative.eval a * H.derivative.eval a *
      w.derivative.derivative.derivative.eval a +
    36 * A.eval a * D.derivative.eval a * H.derivative.derivative.eval a *
      w.derivative.derivative.eval a +
    78 * A.eval a * D.derivative.derivative.eval a * H.derivative.eval a *
      w.derivative.derivative.eval a -
    20 * A.derivative.eval a ^ 2 * B.eval a * H.derivative.eval a *
      w.derivative.derivative.eval a +
    (160 / 9 : k) * A.derivative.eval a * B.eval a ^ 3 *
      H.derivative.eval a ^ 2 * H.derivative.derivative.eval a +
    (160 / 3 : k) * A.derivative.eval a * B.eval a ^ 2 *
      B.derivative.eval a * H.derivative.eval a ^ 3 +
    120 * A.derivative.eval a * D.derivative.eval a * H.derivative.eval a *
      w.derivative.derivative.eval a +
    (80 / 9 : k) * A.derivative.derivative.eval a * B.eval a ^ 3 *
      H.derivative.eval a ^ 3 -
    (320 / 9 : k) * B.eval a ^ 2 * D.derivative.eval a *
      H.derivative.eval a ^ 2 * H.derivative.derivative.eval a -
    (160 / 9 : k) * B.eval a ^ 2 * D.derivative.derivative.eval a *
      H.derivative.eval a ^ 3 -
    (640 / 9 : k) * B.eval a * B.derivative.eval a * D.derivative.eval a *
      H.derivative.eval a ^ 3 +
    90 * B.eval a * gamma * H.derivative.eval a ^ 3 *
      w.derivative.derivative.eval a +
    10 * D.derivative.eval a * H.derivative.eval a *
      phi.derivative.derivative.derivative.eval a

theorem terminalLowerZeroReduced_fourthJet_refinedIII_68
    (H A B D phi w : k[X]) (gamma a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hd : D.eval a = 0) (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0) :
    (terminalLowerZeroReduced68 H A B D phi w gamma).derivative.derivative.derivative.derivative.eval a =
      terminalLowerZeroSixthFace68 H A B D phi w gamma a := by
  simp only [terminalLowerZeroReduced68, terminalLowerZeroSixthFace68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly, eval_add,
    eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    ha, hw, hphi, hd, hw1, hphi1, hphi2, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow]
  ring

theorem eval_sixthDerivative_Hsq_mul_of_four_jets_68
    (H R : k[X]) (a : k) (ha : H.eval a = 0)
    (hR0 : R.eval a = 0) (hR1 : R.derivative.eval a = 0)
    (hR2 : R.derivative.derivative.eval a = 0)
    (hR3 : R.derivative.derivative.derivative.eval a = 0) :
    (H ^ 2 * R).derivative.derivative.derivative.derivative.derivative.derivative.eval a =
      30 * H.derivative.eval a ^ 2 *
        R.derivative.derivative.derivative.derivative.eval a := by
  simp [derivative_mul, derivative_pow, ha, hR0, hR1, hR2, hR3]
  ring

/-- The sixth lower-zero derivative is exactly the vanishing fourth jet of
the reduced polynomial. -/
theorem terminalLowerZeroReduced_fourth_zero_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : D.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hfourth : A.eval a * w.derivative.derivative.eval a =
      (8 / 9 : k) * B.eval a ^ 2 * H.derivative.eval a ^ 2)
    (hlower :
      let C0 := C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
      let E := C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * B ^ 2
      terminalLowerZeroOne68 H A B C0 D E alpha gamma epsilon eta = 0) :
    (terminalLowerZeroReduced68 H A B D phi w gamma).derivative.derivative.derivative.derivative.eval a = 0 := by
  dsimp only at hlower
  let R := terminalLowerZeroReduced68 H A B D phi w gamma
  have hfac := terminalLowerZeroOne_eq_Hsq_reduced_68 H A B D phi w
    alpha gamma epsilon eta
  obtain ⟨hR0, hR1, hR2shape⟩ :=
    terminalLowerZeroReduced_jets_refinedIII_68 H A B D phi w gamma a
      ha hw hphi hd hw1 hphi1 hphi2
  have hR2 : R.derivative.derivative.eval a = 0 := by
    dsimp only [R]
    rw [hR2shape]
    linear_combination (-1 / 3 : k) * A.eval a * B.eval a *
      H.derivative.eval a * hfourth
  have hzero5 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.eval a) hlower
  rw [hfac, derivative_zero, derivative_zero, derivative_zero,
    derivative_zero, derivative_zero, eval_zero] at hzero5
  rw [eval_fifthDerivative_Hsq_mul_of_two_jets_68 H R a ha hR0 hR1,
    hR2, mul_zero, add_zero] at hzero5
  have hc3 : R.derivative.derivative.derivative.eval a = 0 := by
    have hc : 20 * H.derivative.eval a ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)
    exact (mul_eq_zero.mp hzero5).resolve_left hc
  have hzero6 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.derivative.eval a)
      hlower
  rw [hfac, derivative_zero, derivative_zero, derivative_zero,
    derivative_zero, derivative_zero, derivative_zero, eval_zero] at hzero6
  rw [eval_sixthDerivative_Hsq_mul_of_four_jets_68 H R a ha hR0 hR1 hR2 hc3]
      at hzero6
  have hc : 30 * H.derivative.eval a ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)
  exact (mul_eq_zero.mp hzero6).resolve_left hc

/-- A denominator-free resultant eliminating `w''''` and `D''` from the
sixth lower-zero face and I4 orders four and five. -/
theorem terminalRefinedIII_sixth_I4_resultant_68
    (u v n W m d1 w3 m5 x y : k)
    (h6 : u * x + v * y + n = 0)
    (h4 : 36 * W * y + m = 0)
    (h5 : 30 * d1 * x + 60 * w3 * y + m5 = 0) :
    1080 * W * d1 * (36 * W * n - v * m) -
        36 * W * u * (36 * W * m5 - 60 * w3 * m) = 0 := by
  have hx6 : 36 * W * u * x + 36 * W * n - v * m = 0 := by
    linear_combination 36 * W * h6 - v * h4
  have hx5 : 1080 * W * d1 * x + 36 * W * m5 - 60 * w3 * m = 0 := by
    linear_combination 36 * W * h5 - 60 * w3 * h4
  linear_combination 1080 * W * d1 * hx6 - 36 * W * u * hx5

end RefinedIIISixthAlgebra68

section RefinedIIISixthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Actual-source sixth packet.  It does not select or delete any sibling
component. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIISixthLocalPacket
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
    terminalLowerZeroSixthFace68 H A0 b2 D phi w S.gamma a = 0 ∧
    (10 * b2.derivative.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        5 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.derivative.eval a +
        b2.eval a *
          phi.derivative.derivative.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.eval a *
          D.derivative.derivative.derivative.eval a +
        60 * w.derivative.derivative.derivative.eval a *
          D.derivative.derivative.eval a +
        30 * w.derivative.derivative.derivative.derivative.eval a *
          D.derivative.eval a = 0) := by
  have hE := S.terminalActualEShape68 (H := H) A0 C0 E0 b1 b2 w phi
    hb hW hPhi
  have hC : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hshape :
      let C1 := C (1 / 3 : k) * A0 ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k))
      let E1 := C (1 / 27 : k) * A0 ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A0 * w -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 + C (1 / 9 : k) * H ^ 4 * b2 ^ 2
      terminalLowerZeroOne68 H A0 b2 C1 D E1
        S.alpha S.gamma S.epsilon S.eta = 0 := by
    dsimp only
    rw [← hC, ← hE]
    exact hlower
  have hfourth := terminalLowerZeroOne_fourth_refinedIII_factored_face_68
    H A0 b2 D phi w S.alpha S.gamma S.epsilon S.eta a ha hh hA hB hw hph
      hD hw1 hph1 hph2 hshape
  have hR4 := terminalLowerZeroReduced_fourth_zero_68 H A0 b2 D phi w
    S.alpha S.gamma S.epsilon S.eta a ha hh hw hph hD hw1 hph1 hph2
      hfourth hshape
  rw [terminalLowerZeroReduced_fourthJet_refinedIII_68 H A0 b2 D phi w
    S.gamma a ha hw hph hD hw1 hph1 hph2] at hR4
  exact ⟨hR4, terminalI4_fifth_refinedIII_68 b2 D w phi a hw hph hD hw1
    hph1 hph2 hI4⟩

end RefinedIIISixthSource68

end Max11DegreeRoutes
