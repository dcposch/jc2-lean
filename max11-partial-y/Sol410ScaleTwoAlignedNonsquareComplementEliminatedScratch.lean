import Sol410ScaleTwoAlignedNonsquareComplementSourceClosureScratch

/-! # Eliminate both divisor limbs from the aligned `(4,10)` allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- After the `H ∣ g` and `H ∣ (gf+8p₁)` limbs are closed, only the two
same-witness transverse root orientations remain. -/
theorem normalized410ScaleTwo_alignedNonsquare_complementEliminated
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ (g f : K[X]) (x y : K), x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
      p.coeff 3 = H * g ∧
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
      let L := g * f + (8 : K[X]) * p.coeff 1
      (g.eval x = 0 ∧ L.eval x ≠ 0 ∧
          g.eval y ≠ 0 ∧ L.eval y = 0) ∨
        (g.eval x ≠ 0 ∧ L.eval x = 0 ∧
          g.eval y = 0 ∧ L.eval y ≠ 0) := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨g, f, x, y, hxy, hx, hy, hp3, hgf, halloc⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorEliminated
      hsource hnsq haligned
  let L : K[X] := g * f + (8 : K[X]) * p.coeff 1
  refine ⟨g, f, x, y, hxy, hx, hy, hp3, hgf, ?_⟩
  rcases halloc with ⟨l, hL⟩ | htrans
  · exact False.elim
      (normalized410ScaleTwo_alignedNonsquare_complement_false
        hsource hnsq haligned hp3 hgf hL)
  · exact htrans

#print axioms normalized410ScaleTwo_alignedNonsquare_complementEliminated

end Max11DegreeRoutes
