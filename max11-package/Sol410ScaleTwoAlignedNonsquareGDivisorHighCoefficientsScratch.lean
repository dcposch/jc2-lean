import Sol410ScaleTwoAlignedNonsquareRootAllocationDivisorsScratch

/-! # High-coefficient gains on the aligned `(4,10)` `H ∣ g` branch

Once the first two source coefficients gain the core factors furnished by the
two-root allocation, the already-consumed aligned face forces `q₉` to gain
five copies of `H` and `q₈` to gain four.  These are literal identities on the
same normalized source, with no transverse-degree hypothesis.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section HighCoefficientAlgebra410

variable {K : Type*} [Field K] [CharZero K]

/-- Divide the harmless scalar eight after the propagated `H` factors have
been made explicit in the aligned `q₈` row. -/
theorem alignedFinal_gDivisor_highQ410
    (H p2 p3 q8 q9 g1 r : K[X]) (κ : K)
    (hp3 : p3 = H ^ 2 * g1)
    (hp2 : p2 = H * r)
    (hq9 : q9 = Polynomial.C (5 / 2 : K) * p3 * H ^ 3)
    (hq8 : (8 : K[X]) * q8 =
      H * ((15 : K[X]) * p3 ^ 2 + (20 : K[X]) * p2 * H ^ 2 +
        Polynomial.C κ * H ^ 3)) :
    ∃ t8 t9 : K[X], q8 = H ^ 4 * t8 ∧ q9 = H ^ 5 * t9 := by
  let t8 : K[X] := Polynomial.C ((8 : K)⁻¹) *
    ((15 : K[X]) * H * g1 ^ 2 + (20 : K[X]) * r + Polynomial.C κ)
  let t9 : K[X] := Polynomial.C (5 / 2 : K) * g1
  have h8 : (8 : K) ≠ 0 := by norm_num
  have hC8 : (8 : K[X]) = Polynomial.C (8 : K) :=
    Polynomial.C_eq_natCast 8
  have heightInv : (8 : K[X]) * Polynomial.C ((8 : K)⁻¹) = 1 := by
    rw [hC8, ← Polynomial.C_mul, mul_inv_cancel₀ h8, Polynomial.C_1]
  have hq8cleared : (8 : K[X]) * q8 = H ^ 4 *
      ((15 : K[X]) * H * g1 ^ 2 + (20 : K[X]) * r + Polynomial.C κ) := by
    rw [hp3, hp2] at hq8
    linear_combination hq8
  have hq8fact : q8 = H ^ 4 * t8 := by
    calc
      q8 = 1 * q8 := by rw [one_mul]
      _ = ((8 : K[X]) * Polynomial.C ((8 : K)⁻¹)) * q8 := by
        rw [heightInv]
      _ = Polynomial.C ((8 : K)⁻¹) * ((8 : K[X]) * q8) := by ring
      _ = Polynomial.C ((8 : K)⁻¹) *
          (H ^ 4 * ((15 : K[X]) * H * g1 ^ 2 +
            (20 : K[X]) * r + Polynomial.C κ)) := by rw [hq8cleared]
      _ = H ^ 4 * t8 := by
        dsimp only [t8]
        ring
  have hq9fact : q9 = H ^ 5 * t9 := by
    rw [hq9, hp3]
    dsimp only [t9]
    ring
  exact ⟨t8, t9, hq8fact, hq9fact⟩

end HighCoefficientAlgebra410

/-- Source-facing high-coefficient packet for the exact propagated
`H ∣ g` branch.  The original normalized top rows are retained verbatim. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorHighCoefficients
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H g1 r : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hp3deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = H ^ 2 * g1)
    (hp2deep :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 2 = H * r) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (t8 t9 : K[X]),
      p.coeff 4 = H ^ 2 ∧ q.coeff 10 = H ^ 5 ∧
        q.coeff 8 = H ^ 4 * t8 ∧ q.coeff 9 = H ^ 5 * t9 := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, hq9, _hM, hq8⟩ :=
    normalized410ScaleTwo_alignedFace_packet hsource haligned
  obtain ⟨t8, t9, ht8, ht9⟩ := alignedFinal_gDivisor_highQ410
    H (p.coeff 2) (p.coeff 3) (q.coeff 8) (q.coeff 9) g1 r κ
    hp3deep hp2deep hq9 hq8
  exact ⟨κ, t8, t9, hsource.2.2.2.2.1, hsource.2.2.2.2.2.1,
    ht8, ht9⟩

#print axioms alignedFinal_gDivisor_highQ410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorHighCoefficients

end Max11DegreeRoutes
