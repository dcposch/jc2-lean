import Sol410ScaleTwoAlignedNonsquareGDivisorSourceNextCoefficientsScratch

/-! # Lower coefficient propagation on the aligned `(4,10)` divisor limb

The next odd/even defect pair propagates the same exact `H ∣ g` packet to
`q₅` and `q₄`.  The generic algebra is separated from the source-facing
consumer so every source constant and allocation witness remains visible.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section LowerCoefficientAlgebra410

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 4000000 in
/-- After `p₃=H²g₁` and `p₂=Hr`, the fifth and sixth aligned defects
force `H² ∣ q₅` and `H ∣ q₄`. -/
theorem alignedFinal_gDivisor_lowerQ410
    (H p0 p1 p2 p3 q4 q5 q6 q7 g1 r : K[X]) (κ κ3 κ5 : K)
    (hH : H ≠ 0)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ = 0)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM5 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ = 0)
    (hM6 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9) :
    ∃ t4 t5 : K[X], q4 = H * t4 ∧ q5 = H ^ 2 * t5 := by
  let S5 : K[X] :=
    (1920 : K[X]) * p0 * g1 * H + (1920 : K[X]) * p1 * r +
      (480 : K[X]) * p1 * g1 ^ 2 * H +
      (480 : K[X]) * r ^ 2 * g1 * H -
      (80 : K[X]) * r * g1 ^ 3 * H ^ 2 +
      (6 : K[X]) * g1 ^ 5 * H ^ 3 +
      Polynomial.C κ * ((128 : K[X]) * p1 +
        (128 : K[X]) * r * g1 * H) -
      Polynomial.C κ3 * ((6 : K[X]) * g1 * H)
  let S6 : K[X] :=
    (7680 : K[X]) * p0 * r * H +
      (1920 : K[X]) * p0 * g1 ^ 2 * H ^ 2 +
      (3840 : K[X]) * p1 ^ 2 +
      (3840 : K[X]) * p1 * r * g1 * H -
      (320 : K[X]) * p1 * g1 ^ 3 * H ^ 2 +
      (640 : K[X]) * r ^ 3 * H -
      (480 : K[X]) * r ^ 2 * g1 ^ 2 * H ^ 2 +
      (120 : K[X]) * r * g1 ^ 4 * H ^ 3 -
      (10 : K[X]) * g1 ^ 6 * H ^ 4 +
      Polynomial.C κ * ((512 : K[X]) * p0 * H +
        (512 : K[X]) * p1 * g1 * H +
        (256 : K[X]) * r ^ 2 * H) -
      Polynomial.C κ3 * ((6 : K[X]) * g1 ^ 2 * H ^ 2 +
        (24 : K[X]) * r * H) - Polynomial.C κ5 * H
  have hM5raw := hM5
  simp only [alignedFifthDefect410] at hM5raw
  rw [hM4, hM2, hp3, hp2] at hM5raw
  have hq5clear : (512 : K[X]) * q5 = H ^ 2 * S5 := by
    apply mul_right_cancel₀ (pow_ne_zero 5 hH)
    dsimp only [S5]
    linear_combination -hM5raw
  have hM6raw := hM6
  simp only [alignedSixthDefect410] at hM6raw
  rw [hM5, hM4, hM2, hp3, hp2] at hM6raw
  have hq4clear : (2048 : K[X]) * q4 = H * S6 := by
    apply mul_right_cancel₀ (pow_ne_zero 7 hH)
    dsimp only [S6]
    linear_combination -hM6raw
  let t5 : K[X] := Polynomial.C ((512 : K)⁻¹) * S5
  let t4 : K[X] := Polynomial.C ((2048 : K)⁻¹) * S6
  have h512 : (512 : K) ≠ 0 := by norm_num
  have h2048 : (2048 : K) ≠ 0 := by norm_num
  have hC512 : (512 : K[X]) = Polynomial.C (512 : K) :=
    Polynomial.C_eq_natCast 512
  have hC2048 : (2048 : K[X]) = Polynomial.C (2048 : K) :=
    Polynomial.C_eq_natCast 2048
  have h512Inv :
      (512 : K[X]) * Polynomial.C ((512 : K)⁻¹) = 1 := by
    rw [hC512, ← Polynomial.C_mul, mul_inv_cancel₀ h512, Polynomial.C_1]
  have h2048Inv :
      (2048 : K[X]) * Polynomial.C ((2048 : K)⁻¹) = 1 := by
    rw [hC2048, ← Polynomial.C_mul, mul_inv_cancel₀ h2048, Polynomial.C_1]
  have hq5fact : q5 = H ^ 2 * t5 := by
    calc
      q5 = 1 * q5 := by rw [one_mul]
      _ = ((512 : K[X]) * Polynomial.C ((512 : K)⁻¹)) * q5 := by
        rw [h512Inv]
      _ = Polynomial.C ((512 : K)⁻¹) * ((512 : K[X]) * q5) := by ring
      _ = Polynomial.C ((512 : K)⁻¹) * (H ^ 2 * S5) := by
        rw [hq5clear]
      _ = H ^ 2 * t5 := by
        dsimp only [t5]
        ring
  have hq4fact : q4 = H * t4 := by
    calc
      q4 = 1 * q4 := by rw [one_mul]
      _ = ((2048 : K[X]) * Polynomial.C ((2048 : K)⁻¹)) * q4 := by
        rw [h2048Inv]
      _ = Polynomial.C ((2048 : K)⁻¹) * ((2048 : K[X]) * q4) := by ring
      _ = Polynomial.C ((2048 : K)⁻¹) * (H * S6) := by rw [hq4clear]
      _ = H * t4 := by
        dsimp only [t4]
        ring
  exact ⟨t4, t5, hq4fact, hq5fact⟩

end LowerCoefficientAlgebra410

/-- Source-facing four-coefficient propagation on the exact allocation
witnesses. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorLowerCoefficients
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
    ∃ t4 t5 t6 t7 : K[X],
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧
        q.coeff 4 = H * t4 ∧ q.coeff 5 = H ^ 2 * t5 ∧
        q.coeff 6 = H ^ 3 * t6 ∧ q.coeff 7 = H ^ 3 * t7 := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ3, κ5, _κ7, _κ9, _κ11, _g, _f, _hp3, hM2, hM4,
      hM5, hM6, _hM7, _hM8, _hM9, _hM10, _hM11, _hM12, _hgf,
      _hblock⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  obtain ⟨t6, t7, ht6, ht7⟩ := alignedFinal_gDivisor_nextQ410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 6) (q.coeff 7) g1 r κ κ3 hsource.1 hp3deep hp2deep hM2 hM4
  obtain ⟨t4, t5, ht4, ht5⟩ := alignedFinal_gDivisor_lowerQ410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) g1 r κ κ3 κ5
      hsource.1 hp3deep hp2deep hM2 hM4 hM5 hM6
  exact ⟨t4, t5, t6, t7, hg, hp3deep, hp2deep, hf, ht4, ht5, ht6, ht7⟩

#print axioms alignedFinal_gDivisor_lowerQ410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorLowerCoefficients

end Max11DegreeRoutes
