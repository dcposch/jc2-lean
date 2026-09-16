import Fable410ScaleTwoAlignedTenthFacePart03Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- On the aligned face, with the consumed degree-`11` through
degree-`3` rows, the degree-`2` row is the weighted derivative
`2 H M₁₈' - 33 M₁₈ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (33 : K[X]) *
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  rw [hC2, hC3] at hrow
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB8 :=
    alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB10 :=
    alignedSeventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB12 :=
    alignedEighthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB14 :=
    alignedNinthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB16 :=
    alignedTenthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedEleventhDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 0)
    (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12, hB14, hB16] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

#print axioms alignedEleventhDefectRow_eq_zero_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Squared weight-`33/2` polynomial first integral -/

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`33/2` bracket: over a
characteristic-zero field, `2 H D' - 33 D H' = 0` forces
`D² = C c * H³³`. -/
theorem thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410
    {K : Type*} [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (33 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 33 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (33 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC33 : Polynomial.C (33 : K) = (33 : K[X]) :=
      Polynomial.C_eq_natCast 33
    rw [hC2, hC33]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 33) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (33 : K) * H ^ (33 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 33 =
          D * H ^ 32 *
            (Polynomial.C (33 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 33 hH) hW

#print axioms thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Squared weight-`33/2` polynomial first integral of the aligned
`(4,10)` eleventh defect: `M₁₈² = κ₁₀ H³³` — the odd-power
discriminator shape regenerated a FIFTH time, one level below the even
weight-`15` shape of the degree-`3` row. -/
theorem alignedEleventhDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 33 :=
  thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410 hH
    (alignedEleventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

#print axioms alignedEleventhDefectPowerRelation_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Chamber quotients of the thirty-third-power relation -/

set_option maxHeartbeats 64000000 in
/-- In the square chamber `H = h₀²` the thirty-third-power relation
resolves to the literal half-integral form `D = C μ₅ * h₀³³` with
`μ₅² = c`; the scalar `μ₅` is an honest residual and is not cleared. -/
theorem thirtyThirdPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 33) :
    ∃ μ₅ : K, μ₅ ^ 2 = c ∧ D = Polynomial.C μ₅ * h0 ^ 33 := by
  have hdvd : (h0 ^ 33) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h66 := hrel
    rw [hF, hHsq] at h66
    apply mul_left_cancel₀ (pow_ne_zero 66 hh0)
    linear_combination h66
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₅, hμ₅⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₅, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₅ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₅, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₅]
    ring

#print axioms thirtyThirdPower_squareChamber_form_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Parity kill in the nonsquare chamber: the odd exponent of the
thirty-third-power relation forces its constant to vanish, and with it
the whole eleventh defect. -/
theorem thirtyThirdPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 33) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 16) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 32 hH)
    have h32 := hrel
    rw [hG] at h32
    linear_combination h32
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C c := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hc : c = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [ha, zero_mul] at hev
    exact hev.symm
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

#print axioms thirtyThirdPower_nonsquareChamber_kill_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Square chamber -/

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the eleventh defect relation:
cancelling `h₀²²` from `M₁₈ = μ₅ h₀³³` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core
`1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) (u² - 4 p₂)³
+ 30720 h₀² p₁ (33 u⁴ - 72 p₂ u² + 16 p₂²) (u² - 4 p₂)²` carried by
`h₀³` against the explicit quotient, whose leading block is the
μ-loaded octic `13923 u⁸ - 148512 p₂ u⁶ + 524160 p₂² u⁴
- 645120 p₂³ u² + 143360 p₂⁴`.  Neither `M₈` nor `M₁₆` enters, and
the whole relation is `q`-free and `κ`/`κ₅`/`κ₉`-free. -/
theorem alignedSquareEleventh_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ μ₃ κ₇ μ₄ μ₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27)
    (hM18 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C μ₅ * h0 ^ 33) :
    (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 - (104 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * h0 ^ 2 * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
              (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
              (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
              (143360 : K[X]) * a2 ^ 4) +
          h0 * ((1536 : K[X]) * u *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  u ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (2560 : K[X]) * a1 ^ 2 * u ^ 2 *
                (u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 2 *
            (Polynomial.C μ *
                ((209664 : K[X]) * a1 * u ^ 5 -
                  (1290240 : K[X]) * a1 * a2 * u ^ 3 +
                  (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
              Polynomial.C μ₂ *
                ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
                  (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
                  (10240 : K[X]) * a2 ^ 3)) +
          h0 ^ 3 * ((4096 : K[X]) * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                u ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 4 *
            (Polynomial.C μ *
                ((1720320 : K[X]) * a0 * a2 * u ^ 2 -
                  (322560 : K[X]) * a0 * u ^ 4 -
                  (1376256 : K[X]) * a0 * a2 ^ 2 +
                  (860160 : K[X]) * a1 ^ 2 * u ^ 2 -
                  (1376256 : K[X]) * a1 ^ 2 * a2) +
              Polynomial.C μ₂ *
                ((17920 : K[X]) * a1 * u ^ 3 -
                  (61440 : K[X]) * a1 * a2 * u) +
              Polynomial.C μ₃ *
                ((480 : K[X]) * a2 * u ^ 2 - (90 : K[X]) * u ^ 4 -
                  (384 : K[X]) * a2 ^ 2)) +
          h0 ^ 5 * ((64 : K[X]) * u *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2)) +
          h0 ^ 6 *
            (Polynomial.C μ₂ *
                ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
                  (40960 : K[X]) * a1 ^ 2) -
              Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
              Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
              Polynomial.C μ₄ *
                ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2)) +
          h0 ^ 7 *
            (Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
              Polynomial.C κ₇ * ((512 : K[X]) * a1) -
              (125829120 : K[X]) * a0 ^ 2 * a1) +
          h0 ^ 8 *
            (Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
              Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
              Polynomial.C μ₅)) := by
  have hM18' := hM18
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM14, hM12, hM10, hM6, hM4, hM2, hHsq, hp3] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 22 hh0)
  linear_combination hM18'

#print axioms alignedSquareEleventh_core_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`2` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains
`h₀³`, and the peel is EIGHT deep: the NEW μ-loaded octic divisibility
`1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) v³ - μ (13923 u⁸ - 148512 p₂ u⁶
+ 524160 p₂² u⁴ - 645120 p₂³ u² + 143360 p₂⁴) = h₀ s₁₇`, the explicit
peels producing `s₁₈` through `s₂₄` (`s₂₂` is loaded with `μ₄`), and —
with no letter left to solve — the FIRST aligned CONSTANT PIN
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`. -/
theorem alignedSquareEleventh_solved_410 {K : Type*} [Field K]
    [CharZero K] {h0 u v a0 a1 a2 : K[X]} {μ κ₃ μ₂ μ₃ κ₇ μ₄ μ₅ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
              (104 : K[X]) * a2 * u ^ 2 + (48 : K[X]) * a2 ^ 2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (30720 : K[X]) * h0 ^ 2 * a1 *
            ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
              (16 : K[X]) * a2 ^ 2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
                (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
                (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
                (143360 : K[X]) * a2 ^ 4) +
            h0 * ((1536 : K[X]) * u *
              (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
                (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                    u ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
                (2560 : K[X]) * a1 ^ 2 * u ^ 2 *
                  (u ^ 2 - (4 : K[X]) * a2))) +
            h0 ^ 2 *
              (Polynomial.C μ *
                  ((209664 : K[X]) * a1 * u ^ 5 -
                    (1290240 : K[X]) * a1 * a2 * u ^ 3 +
                    (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
                Polynomial.C μ₂ *
                  ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
                    (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
                    (10240 : K[X]) * a2 ^ 3)) +
            h0 ^ 3 * ((4096 : K[X]) * a1 *
              (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
                ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                  u ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
                (1280 : K[X]) * a1 ^ 2 *
                  ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2))) +
            h0 ^ 4 *
              (Polynomial.C μ *
                  ((1720320 : K[X]) * a0 * a2 * u ^ 2 -
                    (322560 : K[X]) * a0 * u ^ 4 -
                    (1376256 : K[X]) * a0 * a2 ^ 2 +
                    (860160 : K[X]) * a1 ^ 2 * u ^ 2 -
                    (1376256 : K[X]) * a1 ^ 2 * a2) +
                Polynomial.C μ₂ *
                  ((17920 : K[X]) * a1 * u ^ 3 -
                    (61440 : K[X]) * a1 * a2 * u) +
                Polynomial.C μ₃ *
                  ((480 : K[X]) * a2 * u ^ 2 - (90 : K[X]) * u ^ 4 -
                    (384 : K[X]) * a2 ^ 2)) +
            h0 ^ 5 * ((64 : K[X]) * u *
              ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                  Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2) +
                ((983040 : K[X]) * a0 -
                  Polynomial.C κ₃ * (3072 : K[X])) * a1 ^ 2)) +
            h0 ^ 6 *
              (Polynomial.C μ₂ *
                  ((81920 : K[X]) * a0 * a2 -
                    (30720 : K[X]) * a0 * u ^ 2 +
                    (40960 : K[X]) * a1 ^ 2) -
                Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
                Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
                Polynomial.C μ₄ *
                  ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2)) +
            h0 ^ 7 *
              (Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
                Polynomial.C κ₇ * ((512 : K[X]) * a1) -
                (125829120 : K[X]) * a0 ^ 2 * a1) +
            h0 ^ 8 *
              (Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
                Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
                Polynomial.C μ₅)))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₁₇ s₁₈ s₁₉ s₂₀ s₂₁ s₂₂ s₂₃ s₂₄ : K[X],
      (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
            (104 : K[X]) * a2 * u ^ 2 + (48 : K[X]) * a2 ^ 2) * v ^ 3 -
          Polynomial.C μ *
            ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
              (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
              (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
              (143360 : K[X]) * a2 ^ 4) = h0 * s₁₇ ∧
      s₁₇ + (30720 : K[X]) * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) * v ^ 2 = h0 * s₁₈ ∧
      s₁₈ + (3932160 : K[X]) * a1 ^ 2 * u ^ 3 * v -
          Polynomial.C μ *
            ((209664 : K[X]) * a1 * u ^ 5 -
              (1290240 : K[X]) * a1 * a2 * u ^ 3 +
              (1720320 : K[X]) * a1 * a2 ^ 2 * u) -
          Polynomial.C μ₂ *
            ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
              (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
              (10240 : K[X]) * a2 ^ 3) = h0 * s₁₉ ∧
      s₁₉ - (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            u ^ 2 - (2949120 : K[X]) * a1 ^ 2) * u * v ^ 2 +
          (5242880 : K[X]) * a1 ^ 3 *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) = h0 * s₂₀ ∧
      s₂₀ - ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
            u * v ^ 3 -
          ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
            a1 * u ^ 2 * v +
          Polynomial.C μ *
            ((322560 : K[X]) * a0 * u ^ 4 -
              (1720320 : K[X]) * a0 * a2 * u ^ 2 +
              (1376256 : K[X]) * a0 * a2 ^ 2 -
              (860160 : K[X]) * a1 ^ 2 * u ^ 2 +
              (1376256 : K[X]) * a1 ^ 2 * a2) -
          Polynomial.C μ₂ *
            ((17920 : K[X]) * a1 * u ^ 3 -
              (61440 : K[X]) * a1 * a2 * u) +
          Polynomial.C μ₃ *
            ((90 : K[X]) * u ^ 4 - (480 : K[X]) * a2 * u ^ 2 +
              (384 : K[X]) * a2 ^ 2) = h0 * s₂₁ ∧
      s₂₁ - ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
            a1 * v ^ 2 -
          ((62914560 : K[X]) * a0 -
            Polynomial.C κ₃ * (196608 : K[X])) * a1 ^ 2 * u =
        h0 * s₂₂ ∧
      s₂₂ - (Polynomial.C κ₃ * ((98304 : K[X]) * a0) +
            Polynomial.C κ₇ * (64 : K[X]) -
            (15728640 : K[X]) * a0 ^ 2) * u * v +
          Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
          Polynomial.C μ₂ *
            ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
              (40960 : K[X]) * a1 ^ 2) +
          Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) -
          Polynomial.C μ₄ *
            ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2) = h0 * s₂₃ ∧
      s₂₃ - Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) -
          Polynomial.C κ₇ * ((512 : K[X]) * a1) +
          (125829120 : K[X]) * a0 ^ 2 * a1 = h0 * s₂₄ ∧
      Polynomial.C μ₅ =
        s₂₄ - Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) -
          Polynomial.C μ₃ * ((3072 : K[X]) * a0) := by
  obtain ⟨s₂₄, hs₂₄⟩ : ∃ w : K[X],
      w = Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
        Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
        Polynomial.C μ₅ := ⟨_, rfl⟩
  obtain ⟨s₂₃, hs₂₃⟩ : ∃ w : K[X],
      w = Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
        Polynomial.C κ₇ * ((512 : K[X]) * a1) -
        (125829120 : K[X]) * a0 ^ 2 * a1 + h0 * s₂₄ := ⟨_, rfl⟩
  obtain ⟨s₂₂, hs₂₂⟩ : ∃ w : K[X],
      w = (Polynomial.C κ₃ * ((98304 : K[X]) * a0) +
          Polynomial.C κ₇ * (64 : K[X]) -
          (15728640 : K[X]) * a0 ^ 2) * u * v -
        Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) +
        Polynomial.C μ₂ *
          ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
            (40960 : K[X]) * a1 ^ 2) -
        Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
        Polynomial.C μ₄ * ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2) +
        h0 * s₂₃ := ⟨_, rfl⟩
  obtain ⟨s₂₁, hs₂₁⟩ : ∃ w : K[X],
      w = ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 * v ^ 2 +
        ((62914560 : K[X]) * a0 - Polynomial.C κ₃ * (196608 : K[X])) *
          a1 ^ 2 * u + h0 * s₂₂ := ⟨_, rfl⟩
  obtain ⟨s₂₀, hs₂₀⟩ : ∃ w : K[X],
      w = ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
          u * v ^ 3 +
        ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
          a1 * u ^ 2 * v -
        Polynomial.C μ *
          ((322560 : K[X]) * a0 * u ^ 4 -
            (1720320 : K[X]) * a0 * a2 * u ^ 2 +
            (1376256 : K[X]) * a0 * a2 ^ 2 -
            (860160 : K[X]) * a1 ^ 2 * u ^ 2 +
            (1376256 : K[X]) * a1 ^ 2 * a2) +
        Polynomial.C μ₂ *
          ((17920 : K[X]) * a1 * u ^ 3 - (61440 : K[X]) * a1 * a2 * u) -
        Polynomial.C μ₃ *
          ((90 : K[X]) * u ^ 4 - (480 : K[X]) * a2 * u ^ 2 +
            (384 : K[X]) * a2 ^ 2) + h0 * s₂₁ := ⟨_, rfl⟩
  obtain ⟨s₁₉, hs₁₉⟩ : ∃ w : K[X],
      w = (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          u ^ 2 - (2949120 : K[X]) * a1 ^ 2) * u * v ^ 2 -
        (5242880 : K[X]) * a1 ^ 3 *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) + h0 * s₂₀ := ⟨_, rfl⟩
  obtain ⟨s₁₈, hs₁₈⟩ : ∃ w : K[X],
      w = -(3932160 : K[X]) * a1 ^ 2 * u ^ 3 * v +
        Polynomial.C μ *
          ((209664 : K[X]) * a1 * u ^ 5 -
            (1290240 : K[X]) * a1 * a2 * u ^ 3 +
            (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
        Polynomial.C μ₂ *
          ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
            (26880 : K[X]) * a2 ^ 2 * u ^ 2 - (10240 : K[X]) * a2 ^ 3) +
        h0 * s₁₉ := ⟨_, rfl⟩
  obtain ⟨s₁₇, hs₁₇⟩ : ∃ w : K[X],
      w = -(30720 : K[X]) * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) * v ^ 2 + h0 * s₁₈ := ⟨_, rfl⟩
  refine ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs₁₇, hs₁₈, hs₁₉, hs₂₀, hs₂₁, hs₂₂, hs₂₃, hs₂₄]
    linear_combination hcore
  · rw [hs₁₇]
    ring
  · rw [hs₁₈]
    ring
  · rw [hs₁₉]
    ring
  · rw [hs₂₀]
    ring
  · rw [hs₂₁]
    ring
  · rw [hs₂₂]
    ring
  · rw [hs₂₃]
    ring
  · rw [hs₂₄]
    ring

#print axioms alignedSquareEleventh_solved_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the eleventh defect relation:
cancelling `H¹¹` from `M₁₈ = 0` (parity kill) on `p₃ = H g`,
`M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₁₂ = κ₇ H¹²` exposes the
same core in `g` carried by `H²` against the explicit quotient — a
`q`-free constraint. -/
theorem alignedNonsquareEleventh_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM180 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
      κ = 0) :
    (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 - (104 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * H * a1 *
          ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        ((1536 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  g ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) -
              (2560 : K[X]) * a1 ^ 2 * g ^ 2) +
          (4096 : K[X]) * H * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2)) +
          (64 : K[X]) * H ^ 2 * g *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2) +
          (512 : K[X]) * H ^ 3 * a1 *
            (Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
              (245760 : K[X]) * a0 ^ 2)) := by
  have hM18' := hM180
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM140, hM12, hM100, hM60, hM4, hM20, hg] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 11 hH)
  linear_combination hM18'

#print axioms alignedNonsquareEleventh_core_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`2` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` the row yields a `q`-free block
identity — the first aligned nonsquare row consuming NO letter.  The
block collapses at the core root to the perfect-cube product
`20480 g² (g f + 8 p₁)³`. -/
theorem alignedNonsquareEleventh_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 : K[X]} {κ₃ κ₇ : K}
    (hH : H ≠ 0)
    (hcore :
      (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
              (104 : K[X]) * a2 * g ^ 2 + (48 : K[X]) * a2 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (30720 : K[X]) * H * a1 *
            ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
              (16 : K[X]) * a2 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          ((1536 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) *
              (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                  (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
                (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                    g ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2) -
                (2560 : K[X]) * a1 ^ 2 * g ^ 2) +
            (4096 : K[X]) * H * a1 *
              (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                  (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
                ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                  g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
                (1280 : K[X]) * a1 ^ 2 *
                  ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2)) +
            (64 : K[X]) * H ^ 2 * g *
              ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                  Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2) +
                ((983040 : K[X]) * a0 -
                  Polynomial.C κ₃ * (3072 : K[X])) * a1 ^ 2) +
            (512 : K[X]) * H ^ 3 * a1 *
              (Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2)))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
          (104 : K[X]) * a2 * g ^ 2 + (48 : K[X]) * a2 ^ 2) * f ^ 3 +
        (30720 : K[X]) * a1 *
          ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
            (16 : K[X]) * a2 ^ 2) * f ^ 2 +
        (3932160 : K[X]) * a1 ^ 2 * g ^ 3 * f +
        (5242880 : K[X]) * a1 ^ 3 *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) =
      H * ((((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            g ^ 2 - (2949120 : K[X]) * a1 ^ 2) * g * f ^ 2 +
        ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
          a1 * g ^ 2 * f +
        ((62914560 : K[X]) * a0 - Polynomial.C κ₃ * (196608 : K[X])) *
          g * a1 ^ 2 +
        H * (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
            g * f ^ 3 +
          ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
            a1 * f ^ 2 +
          (Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
            (245760 : K[X]) * a0 ^ 2) *
            ((64 : K[X]) * g * f + (512 : K[X]) * a1))) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

#print axioms alignedNonsquareEleventh_solved_410

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Source-facing eleventh-row packets -/

set_option maxHeartbeats 64000000 in
/-- Source-facing squared weight-`33/2` integral of a normalized
aligned scale-two `(4,10)` source: the degree-`2` row is consumed into
`M₁₈² = κ₁₀ H³³` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedEleventhRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₆ * H ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₀ * H ^ 33 ∧
        ∀ a : K, H.eval a = 0 →
          (p.coeff 3).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₄, hM6⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₅, hM8⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₆, hM10⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₇, hM12⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀,
    aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14, hM16, hM18,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_packet

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
half-integral form `M₁₈ = μ₅ h₀³³` with `μ₅² = κ₁₀` (honest residual),
the NEW μ-loaded octic divisibility carrying `s₁₇`, the explicit peels
producing `s₁₈` through `s₂₄`, and the constant pin
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`.  The constants `μ`, `κ₃`,
`μ₂`, `κ₅`, `μ₃`, `κ₇`, `μ₄`, `κ₉`, and `μ₅` are preserved, not
cleared. -/
theorem normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ μ₅ : K)
      (u v s₁₇ s₁₈ s₁₉ s₂₀ s₂₁ s₂₂ s₂₃ s₂₄ : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₂ * h0 ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C μ₃ * h0 ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₄ * h0 ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
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
                (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇ ∧
        s₁₇ + (30720 : K[X]) * p.coeff 1 *
            ((33 : K[X]) * u ^ 4 - (72 : K[X]) * p.coeff 2 * u ^ 2 +
              (16 : K[X]) * p.coeff 2 ^ 2) * v ^ 2 = h0 * s₁₈ ∧
        s₁₈ + (3932160 : K[X]) * p.coeff 1 ^ 2 * u ^ 3 * v -
            Polynomial.C μ *
              ((209664 : K[X]) * p.coeff 1 * u ^ 5 -
                (1290240 : K[X]) * p.coeff 1 * p.coeff 2 * u ^ 3 +
                (1720320 : K[X]) * p.coeff 1 * p.coeff 2 ^ 2 * u) -
            Polynomial.C μ₂ *
              ((1540 : K[X]) * u ^ 6 -
                (12320 : K[X]) * p.coeff 2 * u ^ 4 +
                (26880 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                (10240 : K[X]) * p.coeff 2 ^ 3) = h0 * s₁₉ ∧
        s₁₉ - (((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * u ^ 2 -
              (2949120 : K[X]) * p.coeff 1 ^ 2) * u * v ^ 2 +
            (5242880 : K[X]) * p.coeff 1 ^ 3 *
              ((3 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) =
          h0 * s₂₀ ∧
        s₂₀ - ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * u * v ^ 3 -
            ((15728640 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (49152 : K[X])) *
              p.coeff 1 * u ^ 2 * v +
            Polynomial.C μ *
              ((322560 : K[X]) * p.coeff 0 * u ^ 4 -
                (1720320 : K[X]) * p.coeff 0 * p.coeff 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 0 * p.coeff 2 ^ 2 -
                (860160 : K[X]) * p.coeff 1 ^ 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 1 ^ 2 * p.coeff 2) -
            Polynomial.C μ₂ *
              ((17920 : K[X]) * p.coeff 1 * u ^ 3 -
                (61440 : K[X]) * p.coeff 1 * p.coeff 2 * u) +
            Polynomial.C μ₃ *
              ((90 : K[X]) * u ^ 4 -
                (480 : K[X]) * p.coeff 2 * u ^ 2 +
                (384 : K[X]) * p.coeff 2 ^ 2) = h0 * s₂₁ ∧
        s₂₁ - ((3932160 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 * v ^ 2 -
            ((62914560 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (196608 : K[X])) *
              p.coeff 1 ^ 2 * u = h0 * s₂₂ ∧
        s₂₂ - (Polynomial.C κ₃ * ((98304 : K[X]) * p.coeff 0) +
              Polynomial.C κ₇ * (64 : K[X]) -
              (15728640 : K[X]) * p.coeff 0 ^ 2) * u * v +
            Polynomial.C μ *
              ((2752512 : K[X]) * p.coeff 0 * p.coeff 1 * u) -
            Polynomial.C μ₂ *
              ((81920 : K[X]) * p.coeff 0 * p.coeff 2 -
                (30720 : K[X]) * p.coeff 0 * u ^ 2 +
                (40960 : K[X]) * p.coeff 1 ^ 2) +
            Polynomial.C μ₃ * ((768 : K[X]) * p.coeff 1 * u) -
            Polynomial.C μ₄ *
              ((32 : K[X]) * p.coeff 2 - (12 : K[X]) * u ^ 2) =
          h0 * s₂₃ ∧
        s₂₃ - Polynomial.C κ₃ *
              ((786432 : K[X]) * p.coeff 0 * p.coeff 1) -
            Polynomial.C κ₇ * ((512 : K[X]) * p.coeff 1) +
            (125829120 : K[X]) * p.coeff 0 ^ 2 * p.coeff 1 =
          h0 * s₂₄ ∧
        Polynomial.C μ₅ =
          s₂₄ - Polynomial.C μ * ((5505024 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C μ₃ * ((3072 : K[X]) * p.coeff 0) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hDform⟩ :=
    ninthPower_squareChamber_form_410 hH hHsq hrel
  have hdeg1 : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hHdegree, Polynomial.natDegree_pow] at hdegree
    omega
  have hkill0 : ∀ a : K, h0.eval a = 0 → (p.coeff 3).eval a = 0 := by
    intro a ha
    apply alignedThird_rootKill_p3_410 hrel
    rw [hHsq]
    simp only [Polynomial.eval_pow, ha]
    norm_num
  obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
  obtain ⟨u, hu, _hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
  have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
    fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
  obtain ⟨v, hv, _hq4⟩ := alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
    twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14rel⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
    twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
    thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
  have hcore11 :=
    alignedSquareEleventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM10form hM12form hM14form hM18form
  obtain ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hd1, hd2, hd3, hd4,
    hd5, hd6, hd7, hd8, hpin⟩ :=
    alignedSquareEleventh_solved_410 hh0 hcore11 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, u, v, s₁₇, s₁₈, s₁₉,
    s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hp3, hDform, hM4, hM6form, hM8form,
    hM10form, hM12form, hM14form, hM16, hM18form, hv, hd1, hd2, hd3,
    hd4, hd5, hd6, hd7, hd8, hpin⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact nonsquare-chamber eleventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the parity
kill `M₁₈ ≡ 0` (with `κ₁₀ = 0` forced), and the `q`-free block
identity on the fifth face's divisibility `g² - 4 p₂ = H f` — the
first aligned nonsquare row consuming NO letter. -/
theorem normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g f : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
              (104 : K[X]) * p.coeff 2 * g ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * f ^ 3 +
            (30720 : K[X]) * p.coeff 1 *
              ((33 : K[X]) * g ^ 4 - (72 : K[X]) * p.coeff 2 * g ^ 2 +
                (16 : K[X]) * p.coeff 2 ^ 2) * f ^ 2 +
            (3932160 : K[X]) * p.coeff 1 ^ 2 * g ^ 3 * f +
            (5242880 : K[X]) * p.coeff 1 ^ 3 *
              ((3 : K[X]) * g ^ 2 - (4 : K[X]) * p.coeff 2) =
          H * ((((983040 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (3072 : K[X])) * g ^ 2 -
                (2949120 : K[X]) * p.coeff 1 ^ 2) * g * f ^ 2 +
            ((15728640 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (49152 : K[X])) *
              p.coeff 1 * g ^ 2 * f +
            ((62914560 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (196608 : K[X])) *
              g * p.coeff 1 ^ 2 +
            H * (((491520 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (1536 : K[X])) * g * f ^ 3 +
              ((3932160 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 * f ^ 2 +
              (Polynomial.C κ₃ * ((1536 : K[X]) * p.coeff 0) +
                Polynomial.C κ₇ - (245760 : K[X]) * p.coeff 0 ^ 2) *
                ((64 : K[X]) * g * f +
                  (512 : K[X]) * p.coeff 1)))) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₂, hD0⟩ :=
    ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq ha
  have hkill : ∀ a : K, H.eval a = 0 → (p.coeff 3).eval a = 0 :=
    fun a ha => alignedThird_rootKill_p3_410 hrel ha
  obtain ⟨g, hg⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₄, hM60⟩ :=
    fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
  obtain ⟨f, hf, _hq4⟩ :=
    alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₆, hM100⟩ :=
    twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14rel⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₈, hM140⟩ :=
    twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₁₀, hM180⟩ :=
    thirtyThirdPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM18rel
  have hcore11 :=
    alignedNonsquareEleventh_core_410 hH hg hD0 hM4 hM60 hM100 hM12form
      hM140 hM180
  have hblk := alignedNonsquareEleventh_solved_410 hH hcore11 hf
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, hD0, hM4, hM60, hM8form, hM100,
    hM12form, hM140, hM16, hM180, hf, hblk⟩

#print axioms normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet

end Max11DegreeRoutes
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
