import Fable610ScaleTwoAlignedEleventhFacePart05Scratch
import Fable610ScaleTwoAlignedEleventhFacePart10Scratch
import Fable610ScaleTwoAlignedEleventhFacePart12Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Exact nonsquare-chamber eleventh packet of a normalized aligned
scale-two `(6,10)` source: the odd exponent forces `κ₁₀ = 0` and
`Λ ≡ 0`, and the carried divisor cascade bottoms out on the residue
relation — the first `p₀`-loaded relation of the aligned nonsquare
tower, with no new witness and no `q`-coefficient left to solve. -/
theorem normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5 ∧ p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f
      ∧ (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧ (27 : K[X]) * p.coeff 3 - g1 ^
      3 = H * t2 ∧ (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1
      * t2 = H * u ∧ t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧ (243 : K[X]) *
      p.coeff 1 - g1 * u = H * v ∧ (9795520512 : K[X]) * q.coeff 0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v (p.coeff 0) κ κ₃ κ₅ κ₇
      - Polynomial.C κ₉ ∧ (1632586752 : K[X]) * q.coeff 1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 (p.coeff 0) (p.coeff
      1) κ κ₃ κ₅ κ₇ ∧ (15116544 : K[X]) * q.coeff 2 =
      alignedEighthNonsquareSolved610 H g1 t1 t2 u (p.coeff 0) (p.coeff 1)
      κ κ₃ κ₅ - Polynomial.C κ₇ * H ∧ alignedThirdDefect610 H (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (q.coeff 7) κ = 0 ∧ alignedFourthDefect610 H
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff
      7) κ = Polynomial.C κ₃ * H ^ 10 ∧ alignedFifthDefect610 H (p.coeff
      1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ = 0 ∧ alignedSixthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 15
      ∧ alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4) (q.coeff
      5) (q.coeff 6) (q.coeff 7) κ = 0 ∧ alignedEighthDefect610 H (p.coeff
      0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff
      7) κ = Polynomial.C κ₇ * H ^ 20 ∧ alignedNinthDefect610 H (p.coeff
      0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = 0 ∧ alignedTenthDefect610 H (p.coeff 0) (p.coeff
      1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 ∧
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
      alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0) κ κ₅
      κ₇ = 0 := by
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
    normalized610ScaleTwo_alignedTenthFace_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket10
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
    ht2, hu, ht3, hv, hq0, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0,
    hO⟩ := hpacket10
  obtain ⟨κ₁₀, hΛ2⟩ :=
    alignedEleventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hκ₁₀, hΛ0⟩ :=
    alignedNonsquareEleventh_defect_eq_zero_610 hH hHdegree hnsq hΛ2
  have hres :=
    alignedNonsquareEleventh_descent_610 hH hp5 hf hD0 hF0 hG hI0 hJ
      hL0 hΛ0 ht1 ht2 hu ht3 hv
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
    ht2, hu, ht3, hv, hq0, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0,
    hO, hΛ0, hres⟩

end Max11DegreeRoutes
