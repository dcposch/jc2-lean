import Sol410ScaleTwoAlignedFinalKellerRowScratch

/-! # Same-root final packet on the aligned `(4,10)` source

The aligned defect tower and the constant Keller row are now consumed on the
same normalized source and at the same root supplied by the twelfth-row
packet.  The square and nonsquare residuals are deliberately preserved: this
is the exact branch point for the terminal algebra, not a closure claim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- Minimal terminal inventory at the root selected by the aligned tower. -/
def AlignedFinalRootPacket410 {K : Type*} [Field K]
    (p q : K[X][Y]) (H : K[X]) : Prop :=
  ∃ (a j : K), j ≠ 0 ∧ H.eval a = 0 ∧
    (p.coeff 3).eval a = 0 ∧
    (q.coeff 8).derivative.eval a = 0 ∧
    ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
        (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
    ((∃ (h0 u v : K[X]) (mu : K),
        h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
        p.coeff 3 = h0 ^ 2 * u ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        u.eval a ^ 6 * v.eval a ^ 3 = 0 ∧
        ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
          (v.eval a = 0 ∧ mu = 0))) ∨
      ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
        ∃ g f : K[X], p.coeff 3 = H * g ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
          g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          g.eval a ^ 3 *
              (g.eval a * f.eval a +
                (8 : K) * (p.coeff 1).eval a) ^ 3 = 0))

/-- The final Keller row evaluated at the exact root and paired with the
literal chamber residual produced by the aligned tower. -/
theorem normalized410ScaleTwo_alignedFinalRootPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    AlignedFinalRootPacket410 p q H := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hroot :=
    normalized410ScaleTwo_alignedTwelfthRow_rootData hsource haligned
  dsimp only at hroot
  rcases hroot with ⟨a, _kappa, hHa, _hq8, hp3a, hq8da, hchamber⟩
  have hfinal := normalized410ScaleTwo_alignedFinalKellerRow hsource haligned
  dsimp only at hfinal
  rcases hfinal with ⟨j, hj, hrow⟩
  have hrowa := congrArg (fun w : K[X] => w.eval a) hrow
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    at hrowa
  refine ⟨a, j, hj, hHa, hp3a, hq8da, hrowa, ?_⟩
  rcases hchamber with hsquare | hnonsquare
  · rcases hsquare with
      ⟨mu, _mu2, _mu3, _mu4, _kappa3, _kappa5, _kappa7, _kappa9,
        _kappa11, h0, u, v, _s9, _s16, _s25, _s26, _s32, _s33,
        hh0, hHsq, hha, hp3, huv, _hdiv, _hp3d, _hu2, hprod, hdich,
        _hs25raw, _hs25zero, _hs26raw, _hs26zero, _hs32, _hk11,
        _hq0, _hq1, _hq1combo⟩
    exact Or.inl ⟨h0, u, v, mu, hh0, hHsq, hha, hp3, huv, hprod, hdich⟩
  · rcases hnonsquare with
      ⟨hnsq, g, f, hp3, hgf, hga, _hblock, hprod⟩
    exact Or.inr ⟨hnsq, g, f, hp3, hgf, hga, hprod⟩

#print axioms normalized410ScaleTwo_alignedFinalRootPacket

end Max11DegreeRoutes
