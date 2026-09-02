import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIFourthScratch

/-! # Source shape and factored fourth face on refined component III -/

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

section RefinedIIIFourthFactoredAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- The compact differential polynomial left after the exact `H²` factor is
removed from the once-cancelled lower-zero row. -/
def terminalLowerZeroReduced68
    (H A B D phi w : k[X]) (gamma : k) : k[X] :=
  C (3 * gamma) * B * H ^ 3 * w.derivative +
    C (3 / 2 * gamma) * B * H ^ 2 * w * H.derivative +
    C (3 * gamma) * H ^ 3 * w * B.derivative -
    C (2 / 3 : k) * A ^ 2 * B * H * w.derivative +
    A ^ 2 * B * w * H.derivative -
    C (2 / 3 : k) * A ^ 2 * H * w * B.derivative +
    C (4 / 27 : k) * A * B ^ 3 * H ^ 2 * H.derivative +
    C (8 / 9 : k) * A * B ^ 2 * H ^ 3 * B.derivative -
    C (4 / 3 : k) * A * B * H * w * A.derivative +
    C (1 / 2 : k) * A * B * phi * H.derivative +
    C 4 * A * D * H * w.derivative -
    C 3 * A * D * w * H.derivative +
    C 4 * A * H * w * D.derivative +
    C (8 / 27 : k) * B ^ 3 * H ^ 3 * A.derivative -
    C (8 / 27 : k) * B ^ 2 * D * H ^ 2 * H.derivative -
    C (16 / 27 : k) * B ^ 2 * H ^ 3 * D.derivative -
    C (32 / 27 : k) * B * D * H ^ 3 * B.derivative -
    C 9 * B * H ^ 3 * w * w.derivative -
    C (9 / 4 : k) * B * H ^ 2 * w ^ 2 * H.derivative -
    C (1 / 2 : k) * B * H * phi * A.derivative +
    D * H * w * A.derivative + D * H * phi.derivative -
    C (3 / 2 : k) * D * phi * H.derivative -
    C (9 / 2 : k) * H ^ 3 * w ^ 2 * B.derivative +
    H * phi * D.derivative

/-- Exact factorization before taking any high derivative.  This is the
resource-safe replacement for expanding the fourth derivative of the full
lower row in one tactic invocation. -/
theorem terminalLowerZeroOne_eq_Hsq_reduced_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta : k) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2
    terminalLowerZeroOne68 H A B C0 D E alpha gamma epsilon eta =
      H ^ 2 * terminalLowerZeroReduced68 H A B D phi w gamma := by
  dsimp only [terminalLowerZeroReduced68]
  simp only [terminalLowerZeroOne68, terminalLowerZeroSOne68,
    terminalLowerZeroUOne68, terminalLowerZeroDDOne68,
    terminalLowerZeroUDOne68, terminalLowerZeroCDot68,
    terminalLowerZeroTDot68, terminalLowerOneTNumerator68,
    terminalEDerivativeNumerator68, terminalVDerivativeNumerator68,
    terminalVNumerator68, derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_pow, derivative_C, derivative_ofNat,
    C_ofNat_poly]
  apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
  simp only [map_add, map_sub, map_neg, map_mul, map_pow,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one, map_zero]
  have hc2 : RatFunc.C (2 : k) = (2 : RatFunc k) := by
    simpa only [map_zero, zero_add] using
      (map_ofNat (RatFunc.C (K := k)) 2)
  have hc3 : RatFunc.C (3 : k) = (3 : RatFunc k) := by
    simpa only [map_zero, zero_add] using
      (map_ofNat (RatFunc.C (K := k)) 3)
  have hc4 : RatFunc.C (4 : k) = (4 : RatFunc k) := by
    simpa only [map_zero, zero_add] using
      (map_ofNat (RatFunc.C (K := k)) 4)
  have hc5 : RatFunc.C (5 : k) = (5 : RatFunc k) := by
    simpa only [map_zero, zero_add] using
      (map_ofNat (RatFunc.C (K := k)) 5)
  ring_nf
  rw [hc2, hc3, hc4]
  ring

theorem terminalLowerZeroReduced_jets_refinedIII_68
    (H A B D phi w : k[X]) (gamma a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hd : D.eval a = 0) (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0) :
    let R := terminalLowerZeroReduced68 H A B D phi w gamma
    R.eval a = 0 ∧ R.derivative.eval a = 0 ∧
      R.derivative.derivative.eval a =
        (8 / 27 : k) * A.eval a * B.eval a ^ 3 *
          H.derivative.eval a ^ 3 -
          (1 / 3 : k) * A.eval a ^ 2 * B.eval a * H.derivative.eval a *
            w.derivative.derivative.eval a := by
  dsimp only [terminalLowerZeroReduced68]
  simp only [derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly, eval_add,
    eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    ha, hw, hphi, hd, hw1, hphi1, hphi2, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow]
  constructor
  · ring
  constructor <;> ring

theorem terminalLowerZeroOne_fourth_refinedIII_factored_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hw : w.eval a = 0) (hphi : phi.eval a = 0)
    (hd : D.eval a = 0) (hw1 : w.derivative.eval a = 0)
    (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
        C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * B ^ 2
    (terminalLowerZeroOne68 H A B C0 D E alpha gamma epsilon eta).derivative.derivative.derivative.derivative.eval a =
      (32 / 9 : k) * A.eval a * B.eval a ^ 3 *
          H.derivative.eval a ^ 5 -
        4 * A.eval a ^ 2 * B.eval a * H.derivative.eval a ^ 3 *
          w.derivative.derivative.eval a := by
  dsimp only
  rw [terminalLowerZeroOne_eq_Hsq_reduced_68 H A B D phi w
    alpha gamma epsilon eta]
  obtain ⟨hR0, hR1, hR2⟩ :=
    terminalLowerZeroReduced_jets_refinedIII_68 H A B D phi w gamma a
      ha hw hphi hd hw1 hphi1 hphi2
  simp only [derivative_mul, derivative_pow, derivative_ofNat,
    C_ofNat_poly, derivative_add, eval_add, eval_mul, eval_pow, eval_C,
    eval_ofNat, ha, hR0, hR1, hR2, zero_mul, mul_zero, zero_add, add_zero]
  ring

theorem terminalLowerZeroOne_fourth_refinedIII_factored_face_68
    (H A B D phi w : k[X]) (alpha gamma epsilon eta a : k)
    (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0)
    (hA : A.eval a ≠ 0) (hB : B.eval a ≠ 0)
    (hw : w.eval a = 0) (hphi : phi.eval a = 0) (hd : D.eval a = 0)
    (hw1 : w.derivative.eval a = 0) (hphi1 : phi.derivative.eval a = 0)
    (hphi2 : phi.derivative.derivative.eval a = 0)
    (hlower :
      let C0 := C (1 / 3 : k) * A ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
      let E := C (1 / 27 : k) * A ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A * w -
          C (1 / 2 * gamma : k) * A) - C (3 / 4 * epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * B ^ 2
      terminalLowerZeroOne68 H A B C0 D E alpha gamma epsilon eta = 0) :
    A.eval a * w.derivative.derivative.eval a =
      (8 / 9 : k) * B.eval a ^ 2 * H.derivative.eval a ^ 2 := by
  dsimp only at hlower
  have hzero := congrArg (fun P : k[X] =>
    P.derivative.derivative.derivative.derivative.eval a) hlower
  rw [derivative_zero, derivative_zero, derivative_zero, derivative_zero,
    eval_zero, terminalLowerZeroOne_fourth_refinedIII_factored_68
      H A B D phi w alpha gamma epsilon eta a ha hw hphi hd hw1 hphi1 hphi2]
      at hzero
  have hfac : 4 * A.eval a * B.eval a * H.derivative.eval a ^ 3 *
      ((8 / 9 : k) * B.eval a ^ 2 * H.derivative.eval a ^ 2 -
        A.eval a * w.derivative.derivative.eval a) = 0 := by
    linear_combination hzero
  have hcoef : 4 * A.eval a * B.eval a * H.derivative.eval a ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hB)
      (pow_ne_zero 3 hh)
  have hz := (mul_eq_zero.mp hfac).resolve_left hcoef
  linear_combination -hz

end RefinedIIIFourthFactoredAlgebra68

section RefinedIIIFourthSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Re-export of the actual source `E₀` shape from the two already-proved
scaled-coordinate identities. -/
theorem NonsquareAlignedSourceCurveData68.terminalActualEShape68
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (A0 C0 E0 b1 b2 w2 phi2 : k[X])
    (hb : b1 = H * b2)
    (hW : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2)
    (hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H ^ 2 * phi2) :
    E0 = C (1 / 27 : k) * A0 ^ 3 +
      H ^ 2 * (C (3 / 8 : k) * phi2 + C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * H ^ 4 * b2 ^ 2 := by
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
  have hPhi' := hPhi
  rw [hb] at hPhi'
  have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi'
  have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
  dsimp only [terminalScaledPhi68] at hPm
  simp only [map_add, map_sub, map_neg, map_mul, map_pow,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
  linear_combination (3 / 8 : RatFunc k) * hPm +
    (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm

/-- Source-facing local refinement on the surviving nonzero-`r` component.
It packages the actual `E₀` shape, the exact loaded scalar, and the factored
fourth lower-zero face without deleting any sibling component. -/
theorem NonsquareAlignedSourceCurveData68.terminalRefinedIIIFourthLocalPacket
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
  have hE := S.terminalActualEShape68 (H := H) A0 C0 E0 b1 b2 w phi
    hb hW hPhi
  have hloaded := terminalRefinedIII_loaded_of_E_shape_68
    H A0 b2 D phi w E0 K S.gamma S.epsilon j a ha hE hload
  have hC : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hshape : terminalLowerZeroOne68 H A0 b2
      (C (1 / 3 : k) * A0 ^ 2 +
        H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * S.gamma : k))) D
      (C (1 / 27 : k) * A0 ^ 3 +
        H ^ 2 * (C (3 / 8 : k) * phi + C (3 / 2 : k) * A0 * w -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * H ^ 3 +
        C (1 / 9 : k) * H ^ 4 * b2 ^ 2)
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    rw [← hC, ← hE]
    exact hlower
  have hfourth := terminalLowerZeroOne_fourth_refinedIII_factored_face_68
    H A0 b2 D phi w S.alpha S.gamma S.epsilon S.eta a ha hh hA hB
      hw hph hD hw1 hph1 hph2 hshape
  exact ⟨hloaded.1, hloaded.2.1, hfourth, hloaded.2.2⟩

end RefinedIIIFourthSource68

end Max11DegreeRoutes
