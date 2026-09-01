import Sol410ScaleTwoAlignedNonsquareGDivisorP1FactorScratch

/-! # Simultaneous terminal divisors on the aligned `(4,10)` `H ∣ g` limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Once the ninth row supplies `p₁=Hs`, the complementary terminal factor
uses the same original `g,f` witnesses and also contains `H`. -/
theorem alignedFinal_g_p1_complement_gain410
    (H g f p1 g1 s : K[X])
    (hg : g = H * g1) (hp1 : p1 = H * s) :
    ∃ l : K[X], g * f + (8 : K[X]) * p1 = H * l := by
  refine ⟨g1 * f + (8 : K[X]) * s, ?_⟩
  rw [hg, hp1]
  ring

/-- Source-facing simultaneous `H ∣ g` and `H ∣ (gf+8p₁)` packet,
with no witness reselection. -/
theorem normalized410ScaleTwo_alignedNonsquare_gDivisorComplement
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
    ∃ s l : K[X],
      g = H * g1 ∧ p.coeff 3 = H ^ 2 * g1 ∧
        p.coeff 2 = H * r ∧
        f = H * g1 ^ 2 - (4 : K[X]) * r ∧ p.coeff 1 = H * s ∧
        g * f + (8 : K[X]) * p.coeff 1 = H * l := by
  dsimp only at haligned hp3deep hp2deep ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨s, _hg, _hp3, _hp2, _hf, hs⟩ :=
    normalized410ScaleTwo_alignedNonsquare_gDivisorP1Factor
      hsource hnsq haligned hg hp3deep hp2deep hf
  obtain ⟨l, hl⟩ := alignedFinal_g_p1_complement_gain410
    H g f (p.coeff 1) g1 s hg hs
  exact ⟨s, l, hg, hp3deep, hp2deep, hf, hs, hl⟩

#print axioms alignedFinal_g_p1_complement_gain410
#print axioms normalized410ScaleTwo_alignedNonsquare_gDivisorComplement

end Max11DegreeRoutes
