import Fable410ScaleTwoAlignedNinthFacePart13Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`3`
aligned row: BOTH chambers carry the chamber-free form `M₁₆ = κ₉ H¹⁵`;
the square chamber adds the NEW μ-loaded septic divisibility carrying
`s₁₀` on the fifth face's divisibility, the nonsquare chamber adds the
fifth face's divisibility.  Neither chamber is excluded and no closure
is claimed. -/
theorem normalized410ScaleTwo_alignedTenthRow_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₉ : K) (u v s₁₀ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2)
              (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 15 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (16 : K[X]) * ((143 : K[X]) * u ^ 4 -
                (264 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((663 : K[X]) * u ^ 7 -
                  (6552 : K[X]) * p.coeff 2 * u ^ 5 +
                  (20160 : K[X]) * p.coeff 2 ^ 2 * u ^ 3 -
                  (17920 : K[X]) * p.coeff 2 ^ 3 * u) = h0 * s₁₀) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₉ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2)
              (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 15 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, u, v, s₁₀, s₁₁, s₁₂, s₁₃,
      s₁₄, s₁₅, s₁₆, hp3, hM2f, _hM4, _hM6f, _hM8, _hM10f, _hM12f,
      _hM14f, hM16f, hv, hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7,
      _hq0⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₉, u, v, s₁₀, hp3, hM2f, hM16f,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedTenthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, _hM20, _hM4, _hM60, _hM8,
      _hM100, _hM12f, _hM140, hM16f, hf, _hq0⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₉, g, f, hg, hM16f, hf⟩

end Max11DegreeRoutes
