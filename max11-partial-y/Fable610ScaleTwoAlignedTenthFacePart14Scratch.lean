import Fable610ScaleTwoAlignedTenthFacePart102Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Honest square/nonsquare chamber split of the consumed degree-`5`
aligned row (peeled rows, solved `q₀`, and factored defect relations
are in the two chamber packets above).  Neither chamber is excluded
and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedTenthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (μ : K) (w1 f2 e1 e2 u2 e3 s2 : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
          (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
            h0 * s2) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t1 t2 u t3 v : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
          (243 : K[X]) * p.coeff 1 - g1 * u = H * v) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedTenthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, w1, f2, e1, e2, u2,
      e3, s2, _hμ₃, _hM, hp5, hp4, he1, he2, hu2, _hR8, _he3, h27,
      _hR9, hs2, _hR10x, _hQ9, _hD, _hE, _hF, _hG, _hI, _hJ, _hL,
      _hO⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, μ, w1, f2, e1, e2, u2, e3, s2, hp5,
      hp4, he1, he2, hu2, h27, hs2⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedTenthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, _hM, hp5, hf,
      ht1, ht2, hu, ht3, hv, _hq0, _hq1, _hq2, _hD0, _hE, _hF0, _hG,
      _hI0, _hJ, _hL0, _hO⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t1, t2, u, t3, v, hp5, hf, ht1, ht2,
      hu, ht3, hv⟩

end Max11DegreeRoutes
