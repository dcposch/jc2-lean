import Sol410ScaleTwoAlignedNonsquareTransverseNinthScratch

/-! # Eliminate the transverse aligned `(4,10)` allocations -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- Every nonsquare aligned scale-two `(4,10)` source is impossible.  The two
global divisor limbs were closed earlier; in either remaining transverse
orientation, its `g=0, L≠0` root contradicts the exact ninth row. -/
theorem normalized410ScaleTwo_alignedNonsquare_false
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    False := by
  dsimp only at haligned
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨g, f, x, y, _hxy, hx, hy, hp3, hgf, htrans⟩ :=
    normalized410ScaleTwo_alignedNonsquare_complementEliminated
      hsource hnsq haligned
  obtain ⟨R, _hR⟩ :=
    normalized410ScaleTwo_alignedNonsquare_transverseRaw
      hsource hnsq haligned hp3 hgf
  rcases htrans with hleft | hright
  · exact hleft.2.1
      (R.gZero_forces_complementZero x hx hleft.1)
  · exact hright.2.2.2
      (R.gZero_forces_complementZero y hy hright.2.2.1)

#print axioms normalized410ScaleTwo_alignedNonsquare_false

end Max11DegreeRoutes
