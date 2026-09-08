import Fable410ScaleTwoAlignedEighthFacePart15Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`4`
aligned row: the square chamber carries the half-integral form
`M₁₄ = μ₄ h₀²⁷` and the NEW μ-loaded divisibility carrying `s₅`; the
nonsquare chamber carries the parity kill `M₁₄ ≡ 0` and the fifth
face's divisibility.  Neither chamber is excluded and no closure is
claimed. -/
theorem normalized410ScaleTwo_alignedNinthRow_chamberDichotomy
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
      ∃ (κ μ μ₄ : K) (u v s₅ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
              (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C μ₄ * h0 ^ 27 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (80 : K[X]) * u *
                ((11 : K[X]) * u ^ 2 - (12 : K[X]) * p.coeff 2) *
                v ^ 3 -
              Polynomial.C μ *
                ((273 : K[X]) * u ^ 6 -
                  (2520 : K[X]) * p.coeff 2 * u ^ 4 +
                  (6720 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                  (3584 : K[X]) * p.coeff 2 ^ 3) = h0 * s₅) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
              (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedNinthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, u, v, s₅, s₆, s₇, s₈, s₉,
      hp3, hM2f, _hM4, _hM6f, _hM8, _hM10f, _hM12f, hM14f, hv, hd1,
      _hd2, _hd3, _hd4, _hd5, _hq1⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, μ₄, u, v, s₅, hp3, hM2f, hM14f,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedNinthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, g, f, hg, _hM20, _hM4, _hM60, _hM8, _hM100,
      _hM12f, hM140, hf, _hq1⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g, f, hg, hM140, hf⟩

end Max11DegreeRoutes
