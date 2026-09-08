import Fable410ScaleTwoAlignedEleventhFacePart13Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`1`
aligned row: the square chamber carries the chamber-free form
`M₂₀ = κ₁₁ H¹⁸` and the NEW μ-free leading divisibility carrying
`s₂₅` on the fifth face's divisibility; the nonsquare chamber carries
the same chamber-free form and the fifth face's divisibility — the
first aligned row whose integral shape is IDENTICAL in both chambers.
Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_chamberDichotomy
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
      ∃ (κ μ κ₁₁ : K) (u v s₂₅ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
          h0 * s₂₅) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₁₁ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, κ₁₁, u, v, s₁₆, s₂₅,
      s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hp3, hM2f, _hM4, _hM6f,
      _hM8, _hM10f, _hM12f, _hM14f, _hM16f, _hM18f, hM20f, hv, _hq0,
      hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9, _hpin,
      _hcross⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₁₁, u, v, s₂₅, hp3, hM2f,
      hM20f, hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, κ₁₁, g, f, hg, _hM2z, _hM4, _hM6z, _hM8,
      _hM10z, _hM12f, _hM14z, _hM16f, _hM18z, hM20f, hf, _hblk⟩ :=
      hpacket
    exact Or.inr ⟨hnsq, κ, κ₁₁, g, f, hg, hM20f, hf⟩

end Max11DegreeRoutes
