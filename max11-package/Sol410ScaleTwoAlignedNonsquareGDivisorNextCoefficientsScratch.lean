import Sol410ScaleTwoAlignedNonsquareGDivisorHighCoefficientsScratch

/-! # Next coefficient gains on the aligned `(4,10)` `H ∣ g` branch

The first two consumed defect rows propagate the deeper `p₃,p₂` factors to
`q₇` and `q₆`.  This file keeps the literal defect equations as hypotheses;
the source-facing consumer is added only after these exact algebraic gains.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section NextCoefficientAlgebra410

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 2000000 in
/-- On `p₃=H²g₁`, `p₂=Hr`, the zero third defect and the sixth-power fourth
defect force three core factors in each of `q₇,q₆`. -/
theorem alignedFinal_gDivisor_nextQ410
    (H p0 p1 p2 p3 q6 q7 g1 r : K[X]) (κ κ3 : K)
    (hH : H ≠ 0)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ = 0)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6) :
    ∃ t6 t7 : K[X], q6 = H ^ 3 * t6 ∧ q7 = H ^ 3 * t7 := by
  let S7 : K[X] :=
    (5 : K[X]) * H ^ 2 * g1 ^ 3 +
      (60 : K[X]) * H * r * g1 + (40 : K[X]) * p1 +
      Polynomial.C κ * ((4 : K[X]) * H * g1)
  let S6 : K[X] :=
    (320 : K[X]) * p0 + (480 : K[X]) * p1 * g1 +
      (240 : K[X]) * r ^ 2 + (120 : K[X]) * H * r * g1 ^ 2 -
      (5 : K[X]) * H ^ 2 * g1 ^ 4 +
      Polynomial.C κ * ((32 : K[X]) * r + (16 : K[X]) * H * g1 ^ 2) -
      Polynomial.C κ3
  have hM2raw := hM2
  simp only [alignedThirdDefect410] at hM2raw
  rw [hp3, hp2] at hM2raw
  have hq7clear : (16 : K[X]) * q7 = H ^ 3 * S7 := by
    apply mul_left_cancel₀ hH
    dsimp only [S7]
    linear_combination -hM2raw
  have hM4raw := hM4
  simp only [alignedFourthDefect410] at hM4raw
  rw [hM2, hp3, hp2] at hM4raw
  have hq6clear : (128 : K[X]) * q6 = H ^ 3 * S6 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hH)
    dsimp only [S6]
    linear_combination -hM4raw
  let t7 : K[X] := Polynomial.C ((16 : K)⁻¹) * S7
  let t6 : K[X] := Polynomial.C ((128 : K)⁻¹) * S6
  have h16 : (16 : K) ≠ 0 := by norm_num
  have h128 : (128 : K) ≠ 0 := by norm_num
  have hC16 : (16 : K[X]) = Polynomial.C (16 : K) :=
    Polynomial.C_eq_natCast 16
  have hC128 : (128 : K[X]) = Polynomial.C (128 : K) :=
    Polynomial.C_eq_natCast 128
  have h16Inv : (16 : K[X]) * Polynomial.C ((16 : K)⁻¹) = 1 := by
    rw [hC16, ← Polynomial.C_mul, mul_inv_cancel₀ h16, Polynomial.C_1]
  have h128Inv : (128 : K[X]) * Polynomial.C ((128 : K)⁻¹) = 1 := by
    rw [hC128, ← Polynomial.C_mul, mul_inv_cancel₀ h128, Polynomial.C_1]
  have hq7fact : q7 = H ^ 3 * t7 := by
    calc
      q7 = 1 * q7 := by rw [one_mul]
      _ = ((16 : K[X]) * Polynomial.C ((16 : K)⁻¹)) * q7 := by
        rw [h16Inv]
      _ = Polynomial.C ((16 : K)⁻¹) * ((16 : K[X]) * q7) := by ring
      _ = Polynomial.C ((16 : K)⁻¹) * (H ^ 3 * S7) := by rw [hq7clear]
      _ = H ^ 3 * t7 := by
        dsimp only [t7]
        ring
  have hq6fact : q6 = H ^ 3 * t6 := by
    calc
      q6 = 1 * q6 := by rw [one_mul]
      _ = ((128 : K[X]) * Polynomial.C ((128 : K)⁻¹)) * q6 := by
        rw [h128Inv]
      _ = Polynomial.C ((128 : K)⁻¹) * ((128 : K[X]) * q6) := by ring
      _ = Polynomial.C ((128 : K)⁻¹) * (H ^ 3 * S6) := by rw [hq6clear]
      _ = H ^ 3 * t6 := by
        dsimp only [t6]
        ring
  exact ⟨t6, t7, hq6fact, hq7fact⟩

#print axioms alignedFinal_gDivisor_nextQ410

end NextCoefficientAlgebra410

end Max11DegreeRoutes
