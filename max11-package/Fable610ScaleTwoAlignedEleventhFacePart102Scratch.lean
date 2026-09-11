import Fable610ScaleTwoAlignedTenthFacePart102Scratch
import Fable610ScaleTwoAlignedEleventhFacePart101Scratch
import Fable610ScaleTwoAlignedEleventhFacePart03Scratch
import Fable610ScaleTwoAlignedEleventhFacePart09Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`5` rows, the degree-`4` row is the weighted derivative
`2 H Λ' - 55 Λ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H * (alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (55 : K[X]) * alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_610 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5] at hrow
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hJrow :=
    alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hLrow :=
    alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hOrow :=
    alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedEleventhDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hDrow, hErow, hFrow, hGrow, hIrow, hJrow, hLrow, hOrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

set_option maxHeartbeats 8000000 in
/-- Squared weight-`55/2` polynomial first integral of the aligned
`(6,10)` eleventh defect: `Λ² = κ₁₀ H⁵⁵`.  The odd exponent forces a
square/nonsquare chamber split exactly as for `D`, `F`, `I`, and
`L`. -/
theorem alignedEleventhDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 55 := by
  let L : K[X] :=
    alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
    3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (55 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedEleventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC55 : Polynomial.C (55 : K) = (55 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 55) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (55 : K) * H ^ (55 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 55 =
          L * H ^ 54 *
            (Polynomial.C (55 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC55, hC2]
        have hfac :
            (55 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 55 hH) hW

end Max11DegreeRoutes
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
