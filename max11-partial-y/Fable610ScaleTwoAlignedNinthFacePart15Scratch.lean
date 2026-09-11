import Fable610ScaleTwoAlignedNinthFacePart12Scratch
import Fable610ScaleTwoAlignedNinthFacePart10Scratch
import Fable610ScaleTwoAlignedNinthFacePart05Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Exact nonsquare-chamber ninth packet of a normalized aligned
scale-two `(6,10)` source: the odd exponent forces `κ₈ = 0` and
`L ≡ 0`, the carried eighth-face divisor `81 p₂ + 3 g₁² t₁ - g₁ t₂ =
H u` peels the perfect-square head, the NEW divisibility
`t₂ - 6 g₁ t₁ = H t₃` transfers the cubic head, and `q₁` is solved
OUTRIGHT on top of the carried solved `q₂`. -/
theorem normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ : K) (g1 f t1 t2 u t3 : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (1632586752 : K[X]) * q.coeff 1 =
          alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 (p.coeff 0)
            (p.coeff 1) κ κ₃ κ₅ κ₇ ∧
        (15116544 : K[X]) * q.coeff 2 =
          alignedEighthNonsquareSolved610 H g1 t1 t2 u (p.coeff 0)
              (p.coeff 1) κ κ₃ κ₅ -
            Polynomial.C κ₇ * H ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 := by
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
  have hpacket8 :=
    normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket8
  obtain ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, hM, hp5, hf, ht1, ht2, hu,
    _hR8, hq2, hD0, hE, hF0, hG, hI0, hJ⟩ := hpacket8
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk8, hL0⟩ :=
    alignedNonsquareNinth_defect_eq_zero_610 hH hHdegree hnsq hL2
  obtain ⟨t3, ht3, hq1⟩ :=
    alignedNonsquareNinth_descent_610 hH hHdegree hnsq hp5 hf hD0 hE
      hF0 hG hI0 hJ hL0 ht1 ht2 hu
  exact ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, t3, hM, hp5, hf, ht1, ht2,
    hu, ht3, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0⟩

end Max11DegreeRoutes
