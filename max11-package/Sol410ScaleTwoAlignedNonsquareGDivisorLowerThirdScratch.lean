import Sol410ScaleTwoAlignedNonsquareGDivisorLowerCoefficientsScratch

/-! # Seventh/eighth defect propagation on the aligned `(4,10)` divisor limb

The seventh defect forces one core factor in `q₃`.  The eighth has two
genuine order-eleven terms, so it gives an affine congruence for `q₂`
rather than a false divisibility claim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section LowerThirdAlgebra410

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 6000000 in
/-- Exact seventh/eighth-row gain after `p₃=H²g₁`, `p₂=Hr`. -/
theorem alignedFinal_gDivisor_lowerThird410
    (H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 g1 r : K[X])
    (κ κ3 κ5 κ7 : K)
    (hH : H ≠ 0)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ = 0)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM5 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ = 0)
    (hM6 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9)
    (hM7 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ = 0)
    (hM8 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12) :
    ∃ t2 t3 : K[X],
      q3 = H * t3 ∧
        q2 = Polynomial.C ((131072 : K)⁻¹) *
            ((122880 : K[X]) * p1 ^ 2 * r +
              Polynomial.C κ * ((16384 : K[X]) * p1 ^ 2)) + H * t2 := by
  let S7 : K[X] :=
    (122880 : K[X]) * p0 * p1 +
      (61440 : K[X]) * p0 * r * g1 * H +
      (30720 : K[X]) * p1 ^ 2 * g1 +
      (30720 : K[X]) * p1 * r ^ 2 -
      (5120 : K[X]) * p0 * g1 ^ 3 * H ^ 2 -
      (15360 : K[X]) * p1 * r * g1 ^ 2 * H -
      (5120 : K[X]) * r ^ 3 * g1 * H +
      (1920 : K[X]) * p1 * g1 ^ 4 * H ^ 2 +
      (3840 : K[X]) * r ^ 2 * g1 ^ 3 * H ^ 2 -
      (960 : K[X]) * r * g1 ^ 5 * H ^ 3 +
      (80 : K[X]) * g1 ^ 7 * H ^ 4 +
      Polynomial.C κ * ((8192 : K[X]) * p0 * g1 * H +
        (8192 : K[X]) * p1 * r) -
      Polynomial.C κ5 * ((16 : K[X]) * g1 * H) -
      Polynomial.C κ3 * ((384 : K[X]) * p1 +
        (192 : K[X]) * r * g1 * H -
        (16 : K[X]) * g1 ^ 3 * H ^ 2)
  let B8 : K[X] :=
    (122880 : K[X]) * p1 ^ 2 * r +
      Polynomial.C κ * ((16384 : K[X]) * p1 ^ 2)
  let S8 : K[X] :=
    (245760 : K[X]) * p0 ^ 2 +
      (245760 : K[X]) * p0 * p1 * g1 +
      (122880 : K[X]) * p0 * r ^ 2 -
      (61440 : K[X]) * p0 * r * g1 ^ 2 * H -
      (30720 : K[X]) * p1 ^ 2 * g1 ^ 2 -
      (61440 : K[X]) * p1 * r ^ 2 * g1 -
      (5120 : K[X]) * r ^ 4 +
      (7680 : K[X]) * p0 * g1 ^ 4 * H ^ 2 +
      (30720 : K[X]) * p1 * r * g1 ^ 3 * H +
      (15360 : K[X]) * r ^ 3 * g1 ^ 2 * H -
      (3840 : K[X]) * p1 * g1 ^ 5 * H ^ 2 -
      (9600 : K[X]) * r ^ 2 * g1 ^ 4 * H ^ 2 +
      (2240 : K[X]) * r * g1 ^ 6 * H ^ 3 -
      (180 : K[X]) * g1 ^ 8 * H ^ 4 +
      Polynomial.C κ * ((32768 : K[X]) * p0 * r) -
      Polynomial.C κ5 * ((64 : K[X]) * r) -
      Polynomial.C κ3 * ((1536 : K[X]) * p0 +
        (768 : K[X]) * p1 * g1 + (384 : K[X]) * r ^ 2 -
        (192 : K[X]) * r * g1 ^ 2 * H +
        (24 : K[X]) * g1 ^ 4 * H ^ 2) - Polynomial.C κ7
  have hM7raw := hM7
  simp only [alignedSeventhDefect410] at hM7raw
  rw [hM6, hM5, hM4, hM2, hp3, hp2] at hM7raw
  have hq3clear : (32768 : K[X]) * q3 = H * S7 := by
    apply mul_right_cancel₀ (pow_ne_zero 9 hH)
    dsimp only [S7]
    linear_combination -hM7raw
  have hM8raw := hM8
  simp only [alignedEighthDefect410] at hM8raw
  rw [hM7, hM6, hM5, hM4, hM2, hp3, hp2] at hM8raw
  have hq2clear : (131072 : K[X]) * q2 = B8 + H * S8 := by
    apply mul_right_cancel₀ (pow_ne_zero 11 hH)
    dsimp only [B8, S8]
    linear_combination -hM8raw
  let t3 : K[X] := Polynomial.C ((32768 : K)⁻¹) * S7
  let t2 : K[X] := Polynomial.C ((131072 : K)⁻¹) * S8
  have h32768 : (32768 : K) ≠ 0 := by norm_num
  have h131072 : (131072 : K) ≠ 0 := by norm_num
  have hC32768 : (32768 : K[X]) = Polynomial.C (32768 : K) :=
    Polynomial.C_eq_natCast 32768
  have hC131072 : (131072 : K[X]) = Polynomial.C (131072 : K) :=
    Polynomial.C_eq_natCast 131072
  have h32768Inv :
      (32768 : K[X]) * Polynomial.C ((32768 : K)⁻¹) = 1 := by
    rw [hC32768, ← Polynomial.C_mul, mul_inv_cancel₀ h32768,
      Polynomial.C_1]
  have h131072Inv :
      (131072 : K[X]) * Polynomial.C ((131072 : K)⁻¹) = 1 := by
    rw [hC131072, ← Polynomial.C_mul, mul_inv_cancel₀ h131072,
      Polynomial.C_1]
  have hq3fact : q3 = H * t3 := by
    calc
      q3 = 1 * q3 := by rw [one_mul]
      _ = ((32768 : K[X]) * Polynomial.C ((32768 : K)⁻¹)) * q3 := by
        rw [h32768Inv]
      _ = Polynomial.C ((32768 : K)⁻¹) * ((32768 : K[X]) * q3) := by
        ring
      _ = Polynomial.C ((32768 : K)⁻¹) * (H * S7) := by rw [hq3clear]
      _ = H * t3 := by
        dsimp only [t3]
        ring
  have hq2affine : q2 = Polynomial.C ((131072 : K)⁻¹) * B8 + H * t2 := by
    calc
      q2 = 1 * q2 := by rw [one_mul]
      _ = ((131072 : K[X]) * Polynomial.C ((131072 : K)⁻¹)) * q2 := by
        rw [h131072Inv]
      _ = Polynomial.C ((131072 : K)⁻¹) *
          ((131072 : K[X]) * q2) := by ring
      _ = Polynomial.C ((131072 : K)⁻¹) * (B8 + H * S8) := by
        rw [hq2clear]
      _ = Polynomial.C ((131072 : K)⁻¹) * B8 + H * t2 := by
        dsimp only [t2]
        ring
  exact ⟨t2, t3, hq3fact, by simpa only [B8] using hq2affine⟩

end LowerThirdAlgebra410

/-- Source-facing seventh/eighth-row packet on the original allocation
witnesses. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorLowerThird
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H g f g1 r : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hg : g = H * g1)
    (hp3deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = H ^ 2 * g1)
    (hp2deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 2 = H * r)
    (hf : f = H * g1 ^ 2 - (4 : K[X]) * r) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (t2 t3 : K[X]),
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧
        q.coeff 3 = H * t3 ∧
        q.coeff 2 = Polynomial.C ((131072 : K)⁻¹) *
            ((122880 : K[X]) * p.coeff 1 ^ 2 * r +
              Polynomial.C κ * ((16384 : K[X]) * p.coeff 1 ^ 2)) +
          H * t2 := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ3, κ5, κ7, _κ9, _κ11, _g, _f, _hp3, hM2, hM4,
      hM5, hM6, hM7, hM8, _hM9, _hM10, _hM11, _hM12, _hgf,
      _hblock⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  obtain ⟨t2, t3, ht3, ht2⟩ := alignedFinal_gDivisor_lowerThird410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) g1 r κ κ3 κ5 κ7 hsource.1
      hp3deep hp2deep hM2 hM4 hM5 hM6 hM7 hM8
  exact ⟨κ, t2, t3, hg, hp3deep, hp2deep, hf, ht3, ht2⟩

#print axioms alignedFinal_gDivisor_lowerThird410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorLowerThird

end Max11DegreeRoutes
