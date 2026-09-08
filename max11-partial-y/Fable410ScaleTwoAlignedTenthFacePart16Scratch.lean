import Fable410ScaleTwoAlignedTenthFacePart15Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`2`
aligned row: the square chamber carries the half-integral form
`M₁₈ = μ₅ h₀³³` and the NEW μ-loaded octic divisibility carrying
`s₁₇` on the fifth face's divisibility; the nonsquare chamber carries
the parity kill `M₁₈ ≡ 0` and the fifth face's divisibility.  Neither
chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedEleventhRow_chamberDichotomy
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
      ∃ (κ μ μ₅ : K) (u v s₁₇ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
              (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C μ₅ * h0 ^ 33 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
                (104 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((13923 : K[X]) * u ^ 8 -
                  (148512 : K[X]) * p.coeff 2 * u ^ 6 +
                  (524160 : K[X]) * p.coeff 2 ^ 2 * u ^ 4 -
                  (645120 : K[X]) * p.coeff 2 ^ 3 * u ^ 2 +
                  (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
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
      normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, u, v, s₁₇, s₁₈, s₁₉,
      s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hp3, hM2f, _hM4, _hM6f, _hM8, _hM10f,
      _hM12f, _hM14f, _hM16f, hM18f, hv, hd1, _hd2, _hd3, _hd4, _hd5,
      _hd6, _hd7, _hd8, _hpin⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, μ₅, u, v, s₁₇, hp3, hM2f, hM18f,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, _hM20, _hM4, _hM60, _hM8,
      _hM100, _hM12f, _hM140, _hM16f, hM180, hf, _hblk⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g, f, hg, hM180, hf⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_chamberDichotomy

end Max11DegreeRoutes
