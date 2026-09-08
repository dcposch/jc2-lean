import Sol610ScaleTwoAlignedTwelfthCertificateWithCScratch

/-! # Source assembly for the aligned `(6,10)` twelfth defect

This layer instantiates the exact C-extended certificate on one fixed
normalized source.  The integration constant `κ` is the same witness in the
base equation and all nine preceding defects; no chamber or root witness is
reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
/-- The literal degree-three Keller row and all already-consumed defect rows
force the weight-thirty row of the twelfth defect on the same source. -/
theorem normalized610ScaleTwo_alignedTwelfthDefectRow_610
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]} {κ : K}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
        Polynomial.C κ * H ^ 5) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    alignedEvenWeightedRow610 30 H
      (alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
        (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
        (q.coeff 1)) = 0 := by
  dsimp only at haligned hM ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hraw := alignedTwelfthCoefficientJacobianRow_610 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  simp only [alignedTwelfthJacobianRow610, hC2, hC3, hC4] at hraw
  have hraw' :
      (p.coeff 3).derivative * q.coeff 1 +
          (2 : K[X]) * (p.coeff 2).derivative * q.coeff 2 +
          (3 : K[X]) * (p.coeff 1).derivative * q.coeff 3 +
          (4 : K[X]) * (p.coeff 0).derivative * q.coeff 4 -
        ((4 : K[X]) * p.coeff 4 * (q.coeff 0).derivative +
          (3 : K[X]) * p.coeff 3 * (q.coeff 1).derivative +
          (2 : K[X]) * p.coeff 2 * (q.coeff 2).derivative +
          p.coeff 1 * (q.coeff 3).derivative) = 0 := by
    linear_combination hraw
  have hCeq :
      alignedTwelfthBaseEquation610 H (p.coeff 4) (p.coeff 5)
        (q.coeff 8) κ = 0 := by
    simp only [alignedTwelfthBaseEquation610]
    rw [hM]
    exact sub_self _
  have hCrow :
      alignedEvenWeightedRow610 5 H
        (alignedTwelfthBaseEquation610 H (p.coeff 4) (p.coeff 5)
          (q.coeff 8) κ) = 0 := by
    rw [hCeq]
    simp only [alignedEvenWeightedRow610, Polynomial.derivative_zero,
      mul_zero, zero_mul, sub_self]
  have hD := alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hE := alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hF := alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hG := alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hI := alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hJ := alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hL := alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hOmega := alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6' hq10'
    haligned hM
  have hLambda := alignedEleventhDefectRow_eq_zero_610 hp hq hjac hp6'
    hq10' haligned hM
  have hD' : alignedOddWeightedRow610 15 H
      (alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
        (q.coeff 7) κ) = 0 := by
    simpa only [alignedOddWeightedRow610, Nat.cast_ofNat] using hD
  have hE' : alignedEvenWeightedRow610 10 H
      (alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
        (p.coeff 5) (q.coeff 6) (q.coeff 7) κ) = 0 := by
    simpa only [alignedEvenWeightedRow610, Nat.cast_ofNat] using hE
  have hF' : alignedOddWeightedRow610 25 H
      (alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ) =
        0 := by
    simpa only [alignedOddWeightedRow610, Nat.cast_ofNat] using hF
  have hG' : alignedEvenWeightedRow610 15 H
      (alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
        (q.coeff 6) (q.coeff 7) κ) = 0 := by
    simpa only [alignedEvenWeightedRow610, Nat.cast_ofNat] using hG
  have hI' : alignedOddWeightedRow610 35 H
      (alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
        (q.coeff 5) (q.coeff 6) (q.coeff 7) κ) = 0 := by
    simpa only [alignedOddWeightedRow610, Nat.cast_ofNat] using hI
  have hJ' : alignedEvenWeightedRow610 20 H
      (alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
        (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ) = 0 := by
    simpa only [alignedEvenWeightedRow610, Nat.cast_ofNat] using hJ
  have hL' : alignedOddWeightedRow610 45 H
      (alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
        (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ) =
        0 := by
    simpa only [alignedOddWeightedRow610, Nat.cast_ofNat] using hL
  have hOmega' : alignedEvenWeightedRow610 25 H
      (alignedTenthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0) (q.coeff 1)
        (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
        (q.coeff 7) κ) = 0 := by
    simpa only [alignedEvenWeightedRow610, Nat.cast_ofNat] using hOmega
  have hLambda' : alignedOddWeightedRow610 55 H
      (alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
        (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ) =
        0 := by
    simpa only [alignedOddWeightedRow610, Nat.cast_ofNat] using hLambda
  have hid := alignedTwelfthDefect_withC_multiplier_identity_610 H
    (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) (q.coeff 8) κ
  rw [hraw', hCrow, hCeq] at hid
  rw [hD', hE', hF', hG', hI', hJ', hL', hOmega', hLambda'] at hid
  simp only [mul_zero, zero_mul, add_zero] at hid
  have hconst : (16384 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  exact (mul_eq_zero.mp hid.symm).resolve_left hconst

/-- Chamber-free weight-thirty first integral produced by the assembled
twelfth row: `Theta = c H^30` for a retained source constant `c`. -/
theorem normalized610ScaleTwo_alignedTwelfthDefectPowerRelation_610
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]} {κ : K}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
        Polynomial.C κ * H ^ 5) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ c : K,
      alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) =
        Polynomial.C c * H ^ 30 := by
  dsimp only at haligned hM ⊢
  have hrow := normalized610ScaleTwo_alignedTwelfthDefectRow_610 hsource
    haligned hM
  rcases hsource with ⟨hH, _hHdegree, _hPdegree, _hQdegree, _hp6, _hq10,
    _hKeller⟩
  exact thirtiethPowerRelation_of_weightThirtyRow_610 hH hrow

#print axioms normalized610ScaleTwo_alignedTwelfthDefectRow_610
#print axioms normalized610ScaleTwo_alignedTwelfthDefectPowerRelation_610

end Max11DegreeRoutes
