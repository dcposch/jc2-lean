import Sol410ScaleTwoAlignedNonsquareGDivisorNextCoefficientsScratch

/-! # Source-facing next coefficients on the aligned `(4,10)` divisor limb

This attaches the `q₇,q₆` factor gains to the literal normalized source and
to the same `g,f,g₁,r` witnesses produced by the two-root allocation.  No
witness is reselected and the complementary allocation limbs remain separate.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- On the exact `H ∣ g` output of the two-root allocation, the literal third
and fourth aligned defect rows force `H³ ∣ q₇,q₆`. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorNextCoefficients
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
    ∃ (κ κ3 : K) (t6 t7 : K[X]),
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧
        q.coeff 6 = H ^ 3 * t6 ∧ q.coeff 7 = H ^ 3 * t7 := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ3, _κ5, _κ7, _κ9, _κ11, _g, _f, _hp3, hM2, hM4,
      _hM5, _hM6, _hM7, _hM8, _hM9, _hM10, _hM11, _hM12, _hgf,
      _hblock⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  obtain ⟨t6, t7, ht6, ht7⟩ := alignedFinal_gDivisor_nextQ410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 6) (q.coeff 7) g1 r κ κ3 hsource.1 hp3deep hp2deep hM2 hM4
  exact ⟨κ, κ3, t6, t7, hg, hp3deep, hp2deep, hf, ht6, ht7⟩

#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorNextCoefficients

end Max11DegreeRoutes
