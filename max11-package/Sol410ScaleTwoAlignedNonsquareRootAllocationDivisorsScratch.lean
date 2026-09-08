import Sol410ScaleTwoAlignedNonsquareRootAllocationScratch

/-! # Divisor consumers for the aligned `(4,10)` two-root allocation

The first global allocation branch has genuine coefficient content: if the
quadratic core divides `g`, then the retained identities force an additional
core factor in both `p₃` and `p₂`.  The complementary branch is exposed with
its exact quotient, while the two transverse root orientations are preserved.
No degree bound in the transverse variable is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

section DivisorAlgebra410

variable {K : Type*} [Field K] [CharZero K]

/-- A core factor in `g` propagates to the next two source coefficients. -/
theorem alignedFinal_gDivisor_gain410
    (H g f p2 p3 : K[X])
    (hp3 : p3 = H * g)
    (hgf : g ^ 2 - (4 : K[X]) * p2 = H * f)
    (hg : H ∣ g) :
    ∃ g1 r : K[X],
      g = H * g1 ∧ p3 = H ^ 2 * g1 ∧ p2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r := by
  obtain ⟨g1, hg1⟩ := hg
  let r : K[X] := Polynomial.C ((4 : K)⁻¹) * (H * g1 ^ 2 - f)
  have h4 : (4 : K) ≠ 0 := by norm_num
  have hC4 : (4 : K[X]) = Polynomial.C (4 : K) :=
    Polynomial.C_eq_natCast 4
  have hfourInv : (4 : K[X]) * Polynomial.C ((4 : K)⁻¹) = 1 := by
    rw [hC4, ← Polynomial.C_mul, mul_inv_cancel₀ h4, Polynomial.C_1]
  have hfour : (4 : K[X]) * p2 = H * (H * g1 ^ 2 - f) := by
    rw [hg1] at hgf
    linear_combination -hgf
  have hp2 : p2 = H * r := by
    calc
      p2 = 1 * p2 := by rw [one_mul]
      _ = ((4 : K[X]) * Polynomial.C ((4 : K)⁻¹)) * p2 := by
        rw [hfourInv]
      _ = Polynomial.C ((4 : K)⁻¹) * ((4 : K[X]) * p2) := by ring
      _ = Polynomial.C ((4 : K)⁻¹) * (H * (H * g1 ^ 2 - f)) := by
        rw [hfour]
      _ = H * r := by
        dsimp only [r]
        ring
  refine ⟨g1, r, hg1, ?_, hp2, ?_⟩
  · rw [hp3, hg1]
    ring
  · dsimp only [r]
    rw [← mul_assoc, hfourInv, one_mul]
    ring

/-- Name the exact quotient in the complementary allocation branch. -/
theorem alignedFinal_complementDivisor_gain410
    (H g f p1 : K[X])
    (hL : H ∣ g * f + (8 : K[X]) * p1) :
    ∃ l : K[X], g * f + (8 : K[X]) * p1 = H * l := by
  exact hL

end DivisorAlgebra410

/-- Source-facing refinement of the nonsquare two-root allocation.  The first
branch now carries the propagated `p₃,p₂` divisors, the second carries its
named complementary quotient, and neither transverse orientation is lost. -/
theorem normalized410ScaleTwo_alignedNonsquare_rootAllocationDivisors
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (g f : K[X]) (x y : K), x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
      p.coeff 3 = H * g ∧
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
      let L := g * f + (8 : K[X]) * p.coeff 1
      (∃ g1 r : K[X],
          g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
            p.coeff 2 = H * r ∧ f = H * g1 ^ 2 - (4 : K[X]) * r) ∨
        (∃ l : K[X], L = H * l) ∨
        ((g.eval x = 0 ∧ L.eval x ≠ 0 ∧
            g.eval y ≠ 0 ∧ L.eval y = 0) ∨
          (g.eval x ≠ 0 ∧ L.eval x = 0 ∧
            g.eval y = 0 ∧ L.eval y ≠ 0)) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨g, f, x, y, hxy, hx, hy, hp3, hgf, halloc⟩ :=
    normalized410ScaleTwo_alignedNonsquare_rootAllocation
      hsource hnsq haligned
  let L : K[X] := g * f + (8 : K[X]) * p.coeff 1
  refine ⟨g, f, x, y, hxy, hx, hy, hp3, hgf, ?_⟩
  rcases halloc with hg | hL | htrans
  · exact Or.inl (alignedFinal_gDivisor_gain410
      H g f (p.coeff 2) (p.coeff 3) hp3 hgf hg)
  · exact Or.inr (Or.inl
      (alignedFinal_complementDivisor_gain410 H g f (p.coeff 1) hL))
  · exact Or.inr (Or.inr htrans)

#print axioms alignedFinal_gDivisor_gain410
#print axioms normalized410ScaleTwo_alignedNonsquare_rootAllocationDivisors

end Max11DegreeRoutes
