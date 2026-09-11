import Fable610ScaleTwoAlignedTenthFacePart12Scratch
import Fable610ScaleTwoAlignedEleventhFacePart05Scratch
import Fable610ScaleTwoAlignedEleventhFacePart06Scratch
import Fable610ScaleTwoAlignedEleventhFacePart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(6,10)` source: everything from the tenth packet, plus the
square root `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`, the NEW divisibility
`μ w₁⁸ = h₀ s₄`, the peeled eleventh row `= μ₄ h₀⁷` (the first aligned
square row with no `q`-coefficient), and the root-deepened divisor
`μ w₁⁸ = h₀² s₅`. -/
theorem normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ ν κ₅ ν₂ κ₇ κ₈ μ₃ κ₉ κ₁₀ μ₄ : K) (w1 f2 e1 e2 u2 e3 s2 s4
      s5 : K[X]), μ₃ ^ 2 = κ₈ ∧ μ₄ ^ 2 = κ₁₀ ∧ alignedSecondDefect610 H
      (p.coeff 4) (p.coeff 5) (q.coeff 8) = Polynomial.C κ * H ^ 5 ∧
      p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧ (3 : K[X]) * f2
      - w1 ^ 2 = h0 * e1 ∧ (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧ w1
      * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
      alignedEighthSquarePeeledRow610 h0 w1 e1 e2 (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ = Polynomial.C κ₇ * h0 ^ 6 ∧
      e2 = h0 * e3 ∧ (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
      alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0) (p.coeff
      1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ = Polynomial.C μ₃ * h0
      ^ 6 ∧ (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 = h0
      * s2 ∧ alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (q.coeff 0) κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
      Polynomial.C κ₉ * h0 ^ 6 ∧ Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
      alignedEleventhSquarePeeledRow610 h0 w1 e1 e2 u2 s2 s4 (p.coeff 0)
      (p.coeff 1) (p.coeff 2) κ μ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C μ₄ * h0 ^ 7
      ∧ s4 = h0 * s5 ∧ Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 ∧
      alignedEighthSquareCombinedRow610 h0 w1 e1 e2 (p.coeff 0) (p.coeff
      1) (p.coeff 2) (q.coeff 2) (q.coeff 3) κ μ κ₃ ν κ₅ ν₂ = Polynomial.C
      κ₇ * h0 ^ 5 + Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) ∧
      alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      7) κ = Polynomial.C μ * h0 ^ 15 ∧ alignedFourthDefect610 H (p.coeff
      2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C κ₃ * H ^ 10 ∧ alignedFifthDefect610 H (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = Polynomial.C ν * h0 ^ 25 ∧ alignedSixthDefect610
      H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
      (p.coeff 5) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C κ₅ * H ^ 15 ∧ alignedSeventhDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      ν₂ * h0 ^ 35 ∧ alignedEighthDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      κ₇ * H ^ 20 ∧ alignedNinthDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C μ₃ * h0 ^ 45 ∧ alignedTenthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 ∧
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      μ₄ * h0 ^ 55 ∧ alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2
      = Polynomial.C κ₁₀ * H ^ 55 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hpacket10 :=
    normalized610ScaleTwo_alignedTenthFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket10
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, w1, f2, e1, e2, u2, e3,
    s2, hμ₃, hM, hp5w1, hp4f2, he1, he2, hu2, hR8, he3, h27, hR9, hs2,
    hR10x, hQ9, hD, hE, hF, hG, hI, hJ, hL, hO⟩ := hpacket10
  obtain ⟨κ₁₀, hΛ2⟩ :=
    alignedEleventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨μ₄, hμ₄, hΛ⟩ := alignedSquareEleventh_sqrt_610 hh0 hHsq hΛ2
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨s4, s5, hs4, hR11x, hs5, hmu8⟩ :=
    alignedSquareEleventh_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hF
      hG hI hJ hL hΛ he1 he2 hu2 hs2 he3 hR10x
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, κ₁₀, μ₄, w1, f2, e1, e2,
    u2, e3, s2, s4, s5, hμ₃, hμ₄, hM, hp5w1, hp4f2, he1, he2, hu2, hR8,
    he3, h27, hR9, hs2, hR10x, hs4, hR11x, hs5, hmu8, hQ9, hD, hE, hF,
    hG, hI, hJ, hL, hO, hΛ, hΛ2⟩

end Max11DegreeRoutes
