import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIFourthSourceScratch

/-! # The next divided-I4 and factored lower-zero rows on component III -/

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

section RefinedIIIFifthAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def terminalFourthPairAt68 (f g : k[X]) (a : k) : k :=
  f.derivative.derivative.derivative.derivative.eval a * g.eval a +
    4 * f.derivative.derivative.derivative.eval a * g.derivative.eval a +
    6 * f.derivative.derivative.eval a * g.derivative.derivative.eval a +
    4 * f.derivative.eval a * g.derivative.derivative.derivative.eval a +
    f.eval a * g.derivative.derivative.derivative.derivative.eval a

theorem terminalFourthPairAt68_eq (f g : k[X]) (a : k) :
    (f * g).derivative.derivative.derivative.derivative.eval a =
      terminalFourthPairAt68 f g a := by
  simp only [terminalFourthPairAt68, derivative_add, derivative_mul,
    eval_add, eval_mul, eval_ofNat]
  ring

theorem terminalI4_fourth_refinedIII_68
    (b d w phi : k[X]) (a : k)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : d.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hI4 : b * phi + C 6 * w * d = 0) :
    4 * b.derivative.eval a * phi.derivative.derivative.derivative.eval a +
        b.eval a * phi.derivative.derivative.derivative.derivative.eval a +
        24 * w.derivative.derivative.derivative.eval a * d.derivative.eval a +
        36 * w.derivative.derivative.eval a *
          d.derivative.derivative.eval a = 0 := by
  have h4 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_ofNat, eval_zero,
    terminalFourthPairAt68_eq, terminalFourthPairAt68, hw, hphi, hd, hw1,
    hphi1, hphi2, zero_mul, mul_zero, zero_add, add_zero] at h4
  ring_nf at h4 ⊢
  exact h4

theorem terminalI4_third_refinedIII_68
    (b d w phi : k[X]) (a : k)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : d.eval a = 0)
    (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hI4 : b * phi + C 6 * w * d = 0) :
    b.eval a * phi.derivative.derivative.derivative.eval a +
      18 * w.derivative.derivative.eval a * d.derivative.eval a = 0 := by
  have h3 := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_ofNat, eval_zero,
    terminalThirdPairAt68_eq, terminalThirdPairAt68, hw, hphi, hd, hw1,
    hphi1, hphi2, zero_mul, mul_zero, zero_add, add_zero] at h3
  ring_nf at h3 ⊢
  exact h3

theorem terminalLowerZeroReduced_thirdJet_refinedIII_68
    (H A B D phi w : k[X]) (gamma a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hd : D.eval a = 0) (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0) :
    (terminalLowerZeroReduced68 H A B D phi w gamma).derivative.derivative.derivative.eval a =
      -A.eval a ^ 2 * B.eval a * H.derivative.eval a *
          w.derivative.derivative.derivative.eval a +
        A.eval a ^ 2 * B.eval a * H.derivative.derivative.eval a *
          w.derivative.derivative.eval a -
        3 * A.eval a ^ 2 * B.derivative.eval a * H.derivative.eval a *
          w.derivative.derivative.eval a -
        6 * A.eval a * A.derivative.eval a * B.eval a *
          H.derivative.eval a * w.derivative.derivative.eval a +
        (16 / 9 : k) * A.eval a * B.eval a ^ 3 *
          H.derivative.eval a ^ 2 * H.derivative.derivative.eval a +
        8 * A.eval a * B.eval a ^ 2 * B.derivative.eval a *
          H.derivative.eval a ^ 3 +
        (1 / 2 : k) * A.eval a * B.eval a * H.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        27 * A.eval a * D.derivative.eval a * H.derivative.eval a *
          w.derivative.derivative.eval a +
        (8 / 3 : k) * A.derivative.eval a * B.eval a ^ 3 *
          H.derivative.eval a ^ 3 -
        (16 / 3 : k) * B.eval a ^ 2 * D.derivative.eval a *
          H.derivative.eval a ^ 3 := by
  simp only [terminalLowerZeroReduced68, derivative_add, derivative_sub,
    derivative_neg, derivative_mul, derivative_pow, derivative_C,
    derivative_ofNat, C_ofNat_poly, eval_add, eval_sub, eval_neg, eval_mul,
    eval_pow, eval_C, eval_ofNat, eval_zero, ha, hw, hphi, hd, hw1, hphi1,
    hphi2, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
  ring

theorem eval_fifthDerivative_Hsq_mul_of_two_jets_68
    (H R : k[X]) (a : k) (ha : H.eval a = 0)
    (hR0 : R.eval a = 0) (hR1 : R.derivative.eval a = 0) :
    (H ^ 2 * R).derivative.derivative.derivative.derivative.derivative.eval a =
      20 * H.derivative.eval a ^ 2 *
          R.derivative.derivative.derivative.eval a +
        60 * H.derivative.eval a * H.derivative.derivative.eval a *
          R.derivative.derivative.eval a := by
  simp [derivative_mul, derivative_pow, ha, hR0, hR1]
  ring

theorem terminalLowerZeroOne_fifth_refinedIII_relation_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hA : A.eval a ≠ 0) (hB : B.eval a ≠ 0)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : D.eval a = 0)
    (hw1 : w.derivative.eval a = 0) (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hI4 : B * phi + C 6 * w * D = 0)
    (hlower :
      let C0 := C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
      let E := C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * B ^ 2
      terminalLowerZeroOne68 H A B C0 D E alpha gamma epsilon eta = 0) :
    -6 * A.eval a ^ 2 * w.derivative.derivative.derivative.eval a +
        16 * A.eval a * B.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A.eval a * B.eval a * B.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A.derivative.eval a * B.eval a ^ 2 *
          H.derivative.eval a ^ 2 +
        64 * B.eval a * D.derivative.eval a *
          H.derivative.eval a ^ 2 = 0 := by
  dsimp only at hlower
  let R := terminalLowerZeroReduced68 H A B D phi w gamma
  have hfac := terminalLowerZeroOne_eq_Hsq_reduced_68 H A B D phi w
    alpha gamma epsilon eta
  have hzero := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.derivative.eval a) hlower
  rw [hfac, derivative_zero, derivative_zero, derivative_zero,
    derivative_zero, derivative_zero, eval_zero] at hzero
  obtain ⟨hR0, hR1, hR2⟩ :=
    terminalLowerZeroReduced_jets_refinedIII_68 H A B D phi w gamma a
      ha hw hphi hd hw1 hphi1 hphi2
  rw [eval_fifthDerivative_Hsq_mul_of_two_jets_68 H R a ha hR0 hR1]
      at hzero
  have hfourth := terminalLowerZeroOne_fourth_refinedIII_factored_face_68
    H A B D phi w alpha gamma epsilon eta a ha hh hA hB hw hphi hd hw1
      hphi1 hphi2 hlower
  have hR2zero : R.derivative.derivative.eval a = 0 := by
    dsimp only [R]
    rw [hR2]
    linear_combination (-1 / 3 : k) * A.eval a * B.eval a *
      H.derivative.eval a * hfourth
  have hR3zero : R.derivative.derivative.derivative.eval a = 0 := by
    rw [hR2zero, mul_zero, add_zero] at hzero
    have hc : 20 * H.derivative.eval a ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)
    exact (mul_eq_zero.mp hzero).resolve_left hc
  have hR3 := terminalLowerZeroReduced_thirdJet_refinedIII_68
    H A B D phi w gamma a ha hw hphi hd hw1 hphi1 hphi2
  have hI4three := terminalI4_third_refinedIII_68 B D w phi a hw hphi hd
    hw1 hphi1 hphi2 hI4
  dsimp only [R] at hR3zero
  rw [hR3] at hR3zero
  have hfac : B.eval a * H.derivative.eval a *
      (-6 * A.eval a ^ 2 * w.derivative.derivative.derivative.eval a +
        16 * A.eval a * B.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A.eval a * B.eval a * B.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A.derivative.eval a * B.eval a ^ 2 *
          H.derivative.eval a ^ 2 +
        64 * B.eval a * D.derivative.eval a *
          H.derivative.eval a ^ 2) = 0 := by
    linear_combination 6 * hR3zero -
      3 * A.eval a * H.derivative.eval a * hI4three -
      (6 * A.eval a * B.eval a *
          H.derivative.derivative.eval a -
        18 * A.eval a * B.derivative.eval a * H.derivative.eval a -
        36 * A.derivative.eval a * B.eval a * H.derivative.eval a +
        108 * D.derivative.eval a * H.derivative.eval a) * hfourth
  have hcoef : B.eval a * H.derivative.eval a ≠ 0 :=
    mul_ne_zero hB hh
  exact (mul_eq_zero.mp hfac).resolve_left hcoef

end RefinedIIIFifthAlgebra68

section RefinedIIIFifthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Actual-source local packet after taking both the divided-I4 fourth jet and
the resource-safe fifth lower-zero coefficient. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIFifthLocalPacket
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
    (hload :
      terminalThirdTripleMiddleDoubleZeroAt68 b2 w
          (terminalEDerivativeNumerator68 H E0) a -
        terminalThirdPairLeftZeroAt68 D K a =
          6 * j * H.derivative.eval a ^ 3)
    (hlower : terminalLowerZeroOne68 H A0 b2 C0 D E0
      S.alpha S.gamma S.epsilon S.eta = 0) :
    let eDot := terminalEDerivativeNumerator68 H E0
    eDot.eval a = -(1 / 9 : k) * H.derivative.eval a * A0.eval a ^ 3 ∧
    eDot.derivative.eval a =
      -(2 / 9 : k) * H.derivative.eval a * A0.eval a ^ 2 *
          A0.derivative.eval a -
        (1 / 9 : k) * H.derivative.derivative.eval a * A0.eval a ^ 3 ∧
    A0.eval a * w.derivative.derivative.eval a =
      (8 / 9 : k) * b2.eval a ^ 2 * H.derivative.eval a ^ 2 ∧
    (4 * b2.derivative.eval a *
          phi.derivative.derivative.derivative.eval a +
        b2.eval a * phi.derivative.derivative.derivative.derivative.eval a +
        24 * w.derivative.derivative.derivative.eval a * D.derivative.eval a +
        36 * w.derivative.derivative.eval a *
          D.derivative.derivative.eval a = 0) ∧
    (-6 * A0.eval a ^ 2 * w.derivative.derivative.derivative.eval a +
        16 * A0.eval a * b2.eval a ^ 2 * H.derivative.eval a *
          H.derivative.derivative.eval a +
        32 * A0.eval a * b2.eval a * b2.derivative.eval a *
          H.derivative.eval a ^ 2 -
        16 * A0.derivative.eval a * b2.eval a ^ 2 *
          H.derivative.eval a ^ 2 +
        64 * b2.eval a * D.derivative.eval a *
          H.derivative.eval a ^ 2 = 0) ∧
    -3 * H.derivative.eval a * A0.eval a ^ 3 * b2.derivative.eval a *
          w.derivative.derivative.eval a -
        H.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.derivative.eval a -
        6 * H.derivative.eval a * A0.eval a ^ 2 * A0.derivative.eval a *
          b2.eval a * w.derivative.derivative.eval a -
        3 * H.derivative.derivative.eval a * A0.eval a ^ 3 * b2.eval a *
          w.derivative.derivative.eval a -
        9 * (D.derivative.derivative.derivative.eval a * K.eval a +
          3 * D.derivative.derivative.eval a * K.derivative.eval a +
          3 * D.derivative.eval a * K.derivative.derivative.eval a) =
        54 * j * H.derivative.eval a ^ 3 := by
  dsimp only
  have hprev := S.terminalRefinedIIIFourthLocalPacket (H := H)
    A0 C0 E0 b1 b2 D phi w K a hb hW hPhi ha hh hA hB hw hph hD hw1
      hph1 hph2 hload hlower
  have hI4four := terminalI4_fourth_refinedIII_68 b2 D w phi a hw hph hD
    hw1 hph1 hph2 hI4
  have hfifth := terminalLowerZeroOne_fifth_refinedIII_relation_68
    H A0 b2 D phi w S.alpha S.gamma S.epsilon S.eta a ha hh hA hB hw hph
      hD hw1 hph1 hph2 hI4
      (by
        have hE := S.terminalActualEShape68 (H := H) A0 C0 E0 b1 b2 w phi
          hb hW hPhi
        have hC : C0 = C (1 / 3 : k) * A0 ^ 2 +
            H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
          apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
          have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
          dsimp only [terminalScaledW68] at hm
          simp only [map_add, map_sub, map_mul, map_pow,
            RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hm ⊢
          linear_combination (9 / 4 : RatFunc k) * hm
        rw [← hC, ← hE]
        exact hlower)
  exact ⟨hprev.1, hprev.2.1, hprev.2.2.1, hI4four, hfifth,
    hprev.2.2.2⟩

end RefinedIIIFifthSource68

end Max11DegreeRoutes
