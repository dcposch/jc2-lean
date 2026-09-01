import Sol410ScaleTwoAlignedNonsquareComplementSourceNinthScratch
import Sol410ScaleTwoAlignedNonsquareComplementSourceTenthScratch
import Sol410ScaleTwoAlignedNonsquareComplementSourceEleventhScratch
import Sol410ScaleTwoAlignedNonsquareComplementSourceTwelfthDirectScratch

/-! # Source closure of the complementary aligned `(4,10)` branch -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

set_option maxHeartbeats 8000000 in
/-- The complementary divisor selected by the nonsquare root allocation is
impossible on the original normalized source.  All rows use the exact `g,f,l`
witnesses supplied by that allocation; the source packet's internal witnesses
are identified by cancellation of the same nonzero quadratic `H`. -/
theorem normalized410ScaleTwo_alignedNonsquare_complement_false
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H g f l : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hp3 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = H * g)
    (hgf :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f)
    (hL :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      g * f + (8 : K[X]) * p.coeff 1 = H * l) : False := by
  dsimp only at haligned hp3 hgf hL
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨R, _hR⟩ :=
    normalized410ScaleTwo_alignedNonsquare_complementRaw
      hsource hnsq haligned hp3 hgf hL
  have h9 := R.ninthRow
  have h10 := R.tenthRow
  have h11 := R.eleventhRow
  have h12 := R.twelfthRowDirect
  have hdvd :=
    normalized410ScaleTwo_alignedNonsquare_complementTwelfth_of_rows
      hsource hnsq R.kappa3 R.kappa7 R.kappa11 h11 h12
  obtain ⟨v, hv⟩ := hdvd
  obtain ⟨j, hj, hfinal⟩ :=
    normalized410ScaleTwo_alignedFinalKellerRow hsource haligned
  exact alignedNonsquareComplement_finalRow_false_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 0) (q.coeff 1)
      g f l v R.kappa R.kappa3 R.kappa5 R.kappa7 R.kappa9 R.kappa11
      j R.hH hsource.2.1 hnsq R.hL hv h11 h12 h9 h10 hfinal hj

#print axioms normalized410ScaleTwo_alignedNonsquare_complement_false

end Max11DegreeRoutes
