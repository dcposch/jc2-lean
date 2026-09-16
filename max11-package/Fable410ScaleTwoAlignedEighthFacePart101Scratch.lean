import Fable410ScaleTwoAlignedEighthFacePart03Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- On the aligned face, with the consumed degree-`11` through
degree-`5` rows, the degree-`4` row is the weighted derivative
`2 H M₁₄' - 27 M₁₄ H' = 0`. -/
theorem alignedNinthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (27 : K[X]) *
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedNinthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5] at hrow
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
  have hid := alignedNinthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Squared weight-`27/2` polynomial first integral -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Generic Wronskian quotient for the weight-`27/2` bracket: over a
characteristic-zero field, `2 H D' - 27 D H' = 0` forces
`D² = C c * H²⁷`. -/
theorem twentySeventhPowerRelation_of_weightTwentySevenHalfRow_410
    {K : Type*} [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (27 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 27 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (27 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC27 : Polynomial.C (27 : K) = (27 : K[X]) :=
      Polynomial.C_eq_natCast 27
    rw [hC2, hC27]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 27) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (27 : K) * H ^ (27 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 27 =
          D * H ^ 26 *
            (Polynomial.C (27 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 27 hH) hW

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Squared weight-`27/2` polynomial first integral of the aligned
`(4,10)` ninth defect: `M₁₄² = κ₈ H²⁷` — the odd-power discriminator
shape regenerated a FOURTH time, one level below the even weight-`12`
shape of the degree-`5` row. -/
theorem alignedNinthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₈ : K,
      alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₈ * H ^ 27 :=
  twentySeventhPowerRelation_of_weightTwentySevenHalfRow_410 hH
    (alignedNinthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Chamber quotients of the twenty-seventh-power relation -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- In the square chamber `H = h₀²` the twenty-seventh-power relation
resolves to the literal half-integral form `D = C μ₄ * h₀²⁷` with
`μ₄² = c`; the scalar `μ₄` is an honest residual and is not cleared. -/
theorem twentySeventhPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 27) :
    ∃ μ₄ : K, μ₄ ^ 2 = c ∧ D = Polynomial.C μ₄ * h0 ^ 27 := by
  have hdvd : (h0 ^ 27) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h54 := hrel
    rw [hF, hHsq] at h54
    apply mul_left_cancel₀ (pow_ne_zero 54 hh0)
    linear_combination h54
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₄, hμ₄⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₄, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₄ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₄, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₄]
    ring

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Parity kill in the nonsquare chamber: the odd exponent of the
twenty-seventh-power relation forces its constant to vanish, and with
it the whole ninth defect. -/
theorem twentySeventhPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 27) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 13) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 26 hH)
    have h26 := hrel
    rw [hG] at h26
    linear_combination h26
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

/-! ## Square chamber -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared square-core form of the ninth defect relation: cancelling
`h₀¹⁸` from `M₁₄ = μ₄ h₀²⁷` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`,
`M₁₂ = κ₇ H¹²` exposes the `h₀`-free core
`80 u (11 u² - 12 p₂) (u² - 4 p₂)³
+ 2560 h₀² p₁ (7 u² - 4 p₂) (u² - 4 p₂)²` — the fifth face's perfect
cube times a NEW odd cofactor plus a `p₁`-loaded square — carried by
`h₀³` against the explicit quotient, whose leading block is the
μ-loaded sextic `273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u² - 3584 p₂³`. -/
theorem alignedSquareNinth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27) :
    (80 : K[X]) * u * ((11 : K[X]) * u ^ 2 - (12 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (2560 : K[X]) * h0 ^ 2 * a1 *
          ((7 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((273 : K[X]) * u ^ 6 - (2520 : K[X]) * a2 * u ^ 4 +
              (6720 : K[X]) * a2 ^ 2 * u ^ 2 - (3584 : K[X]) * a2 ^ 3) +
          h0 * (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) *
              u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (122880 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 *
            (Polynomial.C μ₂ *
                ((35 : K[X]) * u ^ 4 - (240 : K[X]) * a2 * u ^ 2 +
                  (320 : K[X]) * a2 ^ 2) +
              Polynomial.C μ *
                (a1 * ((4480 : K[X]) * u ^ 3 - (21504 : K[X]) * a2 * u))) +
          h0 ^ 3 *
            (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
                a1 * (u ^ 2 - (4 : K[X]) * a2) -
              (327680 : K[X]) * a1 ^ 3) +
          h0 ^ 4 *
            (Polynomial.C μ₂ * ((640 : K[X]) * a1 * u) +
              Polynomial.C μ *
                ((86016 : K[X]) * a0 * a2 + (43008 : K[X]) * a1 ^ 2 -
                  (10752 : K[X]) * a0 * u ^ 2) -
              Polynomial.C μ₃ *
                ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * a2))) +
          h0 ^ 5 *
            ((1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * u) +
              Polynomial.C κ₅ * ((512 : K[X]) * a1) +
              Polynomial.C κ₃ * ((6144 : K[X]) * a0 * u) -
              (983040 : K[X]) * a0 ^ 2 * u -
              Polynomial.C κ * ((262144 : K[X]) * a0 * a1)) +
          h0 ^ 6 *
            (Polynomial.C μ₄ + Polynomial.C μ₂ * ((2560 : K[X]) * a0))) := by
  have hM14' := hM14
  simp only [alignedNinthDefect410] at hM14'
  rw [hM12, hM10, hM8, hM6, hM4, hM2, hHsq, hp3] at hM14'
  apply mul_left_cancel₀ (pow_ne_zero 18 hh0)
  linear_combination hM14'

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`4` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains `h₀³`,
and the peel is FIVE deep: the NEW μ-loaded divisibility
`80 u (11 u² - 12 p₂) v³ - μ (273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u²
- 3584 p₂³) = h₀ s₅` — self-similar to the sixth and seventh face
divisibilities one level down — then the explicit peels producing `s₆`,
`s₇`, `s₈`, `s₉`, and the solved linear row.  The new letter `q₁`
carries no `h₀` factor, and `κ₇` enters the solved row at level
zero. -/
theorem alignedSquareNinth_solved_410 {K : Type*} [Field K] [CharZero K]
    {h0 u v a0 a1 a2 b1 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (80 : K[X]) * u * ((11 : K[X]) * u ^ 2 - (12 : K[X]) * a2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (2560 : K[X]) * h0 ^ 2 * a1 *
            ((7 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((273 : K[X]) * u ^ 6 - (2520 : K[X]) * a2 * u ^ 4 +
                (6720 : K[X]) * a2 ^ 2 * u ^ 2 - (3584 : K[X]) * a2 ^ 3) +
            h0 * (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) *
                u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (122880 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            h0 ^ 2 *
              (Polynomial.C μ₂ *
                  ((35 : K[X]) * u ^ 4 - (240 : K[X]) * a2 * u ^ 2 +
                    (320 : K[X]) * a2 ^ 2) +
                Polynomial.C μ *
                  (a1 * ((4480 : K[X]) * u ^ 3 -
                    (21504 : K[X]) * a2 * u))) +
            h0 ^ 3 *
              (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
                  a1 * (u ^ 2 - (4 : K[X]) * a2) -
                (327680 : K[X]) * a1 ^ 3) +
            h0 ^ 4 *
              (Polynomial.C μ₂ * ((640 : K[X]) * a1 * u) +
                Polynomial.C μ *
                  ((86016 : K[X]) * a0 * a2 + (43008 : K[X]) * a1 ^ 2 -
                    (10752 : K[X]) * a0 * u ^ 2) -
                Polynomial.C μ₃ *
                  ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * a2))) +
            h0 ^ 5 *
              ((1048576 : K[X]) * b1 +
                Polynomial.C κ₇ * ((4 : K[X]) * u) +
                Polynomial.C κ₅ * ((512 : K[X]) * a1) +
                Polynomial.C κ₃ * ((6144 : K[X]) * a0 * u) -
                (983040 : K[X]) * a0 ^ 2 * u -
                Polynomial.C κ * ((262144 : K[X]) * a0 * a1)) +
            h0 ^ 6 *
              (Polynomial.C μ₄ +
                Polynomial.C μ₂ * ((2560 : K[X]) * a0))))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₅ s₆ s₇ s₈ s₉ : K[X],
      (80 : K[X]) * u * ((11 : K[X]) * u ^ 2 - (12 : K[X]) * a2) *
            v ^ 3 -
          Polynomial.C μ *
            ((273 : K[X]) * u ^ 6 - (2520 : K[X]) * a2 * u ^ 4 +
              (6720 : K[X]) * a2 ^ 2 * u ^ 2 - (3584 : K[X]) * a2 ^ 3) =
        h0 * s₅ ∧
      s₅ + (2560 : K[X]) * a1 *
          ((7 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 = h0 * s₆ ∧
      s₆ + (122880 : K[X]) * a1 ^ 2 * u * v -
          Polynomial.C μ₂ *
            ((35 : K[X]) * u ^ 4 - (240 : K[X]) * a2 * u ^ 2 +
              (320 : K[X]) * a2 ^ 2) -
          Polynomial.C μ *
            (a1 * ((4480 : K[X]) * u ^ 3 - (21504 : K[X]) * a2 * u)) =
        h0 * s₇ ∧
      s₇ - ((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * u *
            v ^ 2 +
          (327680 : K[X]) * a1 ^ 3 = h0 * s₈ ∧
      s₈ - ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
            a1 * v -
          Polynomial.C μ₂ * ((640 : K[X]) * a1 * u) -
          Polynomial.C μ *
            ((86016 : K[X]) * a0 * a2 + (43008 : K[X]) * a1 ^ 2 -
              (10752 : K[X]) * a0 * u ^ 2) +
          Polynomial.C μ₃ * ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * a2)) =
        h0 * s₉ ∧
      (1048576 : K[X]) * b1 =
        s₉ - Polynomial.C κ₇ * ((4 : K[X]) * u) -
          Polynomial.C κ₅ * ((512 : K[X]) * a1) -
          Polynomial.C κ₃ * ((6144 : K[X]) * a0 * u) +
          (983040 : K[X]) * a0 ^ 2 * u +
          Polynomial.C κ * ((262144 : K[X]) * a0 * a1) -
          h0 * (Polynomial.C μ₄ +
            Polynomial.C μ₂ * ((2560 : K[X]) * a0)) := by
  obtain ⟨s₉, hs₉⟩ : ∃ w : K[X],
      w = (1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * u) +
        Polynomial.C κ₅ * ((512 : K[X]) * a1) +
        Polynomial.C κ₃ * ((6144 : K[X]) * a0 * u) -
        (983040 : K[X]) * a0 ^ 2 * u -
        Polynomial.C κ * ((262144 : K[X]) * a0 * a1) +
        h0 * (Polynomial.C μ₄ +
          Polynomial.C μ₂ * ((2560 : K[X]) * a0)) := ⟨_, rfl⟩
  obtain ⟨s₈, hs₈⟩ : ∃ w : K[X],
      w = ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
          a1 * v +
        Polynomial.C μ₂ * ((640 : K[X]) * a1 * u) +
        Polynomial.C μ *
          ((86016 : K[X]) * a0 * a2 + (43008 : K[X]) * a1 ^ 2 -
            (10752 : K[X]) * a0 * u ^ 2) -
        Polynomial.C μ₃ * ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * a2)) +
        h0 * s₉ := ⟨_, rfl⟩
  obtain ⟨s₇, hs₇⟩ : ∃ w : K[X],
      w = ((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * u *
          v ^ 2 -
        (327680 : K[X]) * a1 ^ 3 + h0 * s₈ := ⟨_, rfl⟩
  obtain ⟨s₆, hs₆⟩ : ∃ w : K[X],
      w = -(122880 : K[X]) * a1 ^ 2 * u * v +
        Polynomial.C μ₂ *
          ((35 : K[X]) * u ^ 4 - (240 : K[X]) * a2 * u ^ 2 +
            (320 : K[X]) * a2 ^ 2) +
        Polynomial.C μ *
          (a1 * ((4480 : K[X]) * u ^ 3 - (21504 : K[X]) * a2 * u)) +
        h0 * s₇ := ⟨_, rfl⟩
  obtain ⟨s₅, hs₅⟩ : ∃ w : K[X],
      w = -(2560 : K[X]) * a1 *
          ((7 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 +
        h0 * s₆ := ⟨_, rfl⟩
  refine ⟨s₅, s₆, s₇, s₈, s₉, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs₅, hs₆, hs₇, hs₈, hs₉]
    linear_combination hcore
  · rw [hs₅]
    ring
  · rw [hs₆]
    ring
  · rw [hs₇]
    ring
  · rw [hs₈]
    ring
  · rw [hs₉]
    ring

/-! ## Nonsquare chamber -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Cleared nonsquare-core form of the ninth defect relation:
cancelling `H⁹` from the parity kill `M₁₄ ≡ 0` on `p₃ = H g`,
`M₂ = 0`, `M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`, `M₁₀ = 0`,
`M₁₂ = κ₇ H¹²` exposes the same core in `g` carried by `H²` against
the explicit quotient. -/
theorem alignedNonsquareNinth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0) :
    (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 - (12 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (2560 : K[X]) * H * a1 *
          ((7 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * g *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
          (122880 : K[X]) * a1 ^ 2 * g * (g ^ 2 - (4 : K[X]) * a2) +
          H * (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
              a1 * (g ^ 2 - (4 : K[X]) * a2) -
            (327680 : K[X]) * a1 ^ 3) +
          H ^ 2 *
            ((1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * g) +
              Polynomial.C κ₅ * ((512 : K[X]) * a1) +
              Polynomial.C κ₃ * ((6144 : K[X]) * a0 * g) -
              (983040 : K[X]) * a0 ^ 2 * g -
              Polynomial.C κ * ((262144 : K[X]) * a0 * a1))) := by
  have hM14' := hM140
  simp only [alignedNinthDefect410] at hM14'
  rw [hM12, hM100, hM8, hM60, hM4, hM20, hg] at hM14'
  apply mul_left_cancel₀ (pow_ne_zero 9 hH)
  linear_combination hM14'

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`4` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` of the fifth face the row does NOT
solve outright — the FIRST nonsquare row needing its own descent: the
septic block
`80 g (11 g² - 12 p₂) f³ + 2560 p₁ (7 g² - 4 p₂) f² + 122880 p₁² g f
+ 327680 p₁³` is an exact `H`-multiple of the explicit quotient
carrying `q₁`, so `q₁` is consumed with an `H`-cofactor (tied, not
solved). -/
theorem alignedNonsquareNinth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 b1 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (hH : H ≠ 0)
    (hcore :
      (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 - (12 : K[X]) * a2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (2560 : K[X]) * H * a1 *
            ((7 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * g *
              (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (122880 : K[X]) * a1 ^ 2 * g * (g ^ 2 - (4 : K[X]) * a2) +
            H * (((491520 : K[X]) * a0 -
                Polynomial.C κ₃ * (1536 : K[X])) *
                a1 * (g ^ 2 - (4 : K[X]) * a2) -
              (327680 : K[X]) * a1 ^ 3) +
            H ^ 2 *
              ((1048576 : K[X]) * b1 +
                Polynomial.C κ₇ * ((4 : K[X]) * g) +
                Polynomial.C κ₅ * ((512 : K[X]) * a1) +
                Polynomial.C κ₃ * ((6144 : K[X]) * a0 * g) -
                (983040 : K[X]) * a0 ^ 2 * g -
                Polynomial.C κ * ((262144 : K[X]) * a0 * a1))))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (80 : K[X]) * g * ((11 : K[X]) * g ^ 2 - (12 : K[X]) * a2) * f ^ 3 +
        (2560 : K[X]) * a1 * ((7 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          f ^ 2 +
        (122880 : K[X]) * a1 ^ 2 * g * f + (327680 : K[X]) * a1 ^ 3 =
      H * (((30720 : K[X]) * a0 - Polynomial.C κ₃ * (96 : K[X])) * g *
          f ^ 2 +
        ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) * a1 *
          f +
        (1048576 : K[X]) * b1 + Polynomial.C κ₇ * ((4 : K[X]) * g) +
        Polynomial.C κ₅ * ((512 : K[X]) * a1) +
        Polynomial.C κ₃ * ((6144 : K[X]) * a0 * g) -
        (983040 : K[X]) * a0 ^ 2 * g -
        Polynomial.C κ * ((262144 : K[X]) * a0 * a1)) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing ninth-row packets -/

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Source-facing squared weight-`27/2` integral of a normalized
aligned scale-two `(4,10)` source: the degree-`4` row is consumed into
`M₁₄² = κ₈ H²⁷` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedNinthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ : K,
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
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact square-chamber ninth packet of a normalized aligned scale-two
`(4,10)` source: the identifying chamber data, the half-integral form
`M₁₄ = μ₄ h₀²⁷` with `μ₄² = κ₈` (honest residual), the NEW μ-loaded
divisibility
`80 u (11 u² - 12 p₂) v³ - μ (273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u²
- 3584 p₂³) = h₀ s₅`, the explicit peels producing `s₆`, `s₇`, `s₈`,
`s₉`, and the solved linear row.  The constants `μ`, `κ₃`, `μ₂`, `κ₅`,
`μ₃`, `κ₇`, and `μ₄` are preserved, not cleared, and `q₁` carries no
`h₀` factor. -/
theorem normalized410ScaleTwo_alignedNinthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ : K) (u v s₅ s₆ s₇ s₈ s₉ : K[X]),
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
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (80 : K[X]) * u *
              ((11 : K[X]) * u ^ 2 - (12 : K[X]) * p.coeff 2) * v ^ 3 -
            Polynomial.C μ *
              ((273 : K[X]) * u ^ 6 -
                (2520 : K[X]) * p.coeff 2 * u ^ 4 +
                (6720 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                (3584 : K[X]) * p.coeff 2 ^ 3) = h0 * s₅ ∧
        s₅ + (2560 : K[X]) * p.coeff 1 *
            ((7 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) * v ^ 2 =
          h0 * s₆ ∧
        s₆ + (122880 : K[X]) * p.coeff 1 ^ 2 * u * v -
            Polynomial.C μ₂ *
              ((35 : K[X]) * u ^ 4 - (240 : K[X]) * p.coeff 2 * u ^ 2 +
                (320 : K[X]) * p.coeff 2 ^ 2) -
            Polynomial.C μ *
              (p.coeff 1 *
                ((4480 : K[X]) * u ^ 3 -
                  (21504 : K[X]) * p.coeff 2 * u)) = h0 * s₇ ∧
        s₇ - ((30720 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (96 : K[X])) * u * v ^ 2 +
            (327680 : K[X]) * p.coeff 1 ^ 3 = h0 * s₈ ∧
        s₈ - ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * p.coeff 1 * v -
            Polynomial.C μ₂ * ((640 : K[X]) * p.coeff 1 * u) -
            Polynomial.C μ *
              ((86016 : K[X]) * p.coeff 0 * p.coeff 2 +
                (43008 : K[X]) * p.coeff 1 ^ 2 -
                (10752 : K[X]) * p.coeff 0 * u ^ 2) +
            Polynomial.C μ₃ *
              ((3 : K[X]) * (u ^ 2 - (8 : K[X]) * p.coeff 2)) =
          h0 * s₉ ∧
        (1048576 : K[X]) * q.coeff 1 =
          s₉ - Polynomial.C κ₇ * ((4 : K[X]) * u) -
            Polynomial.C κ₅ * ((512 : K[X]) * p.coeff 1) -
            Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0 * u) +
            (983040 : K[X]) * p.coeff 0 ^ 2 * u +
            Polynomial.C κ * ((262144 : K[X]) * p.coeff 0 * p.coeff 1) -
            h0 * (Polynomial.C μ₄ +
              Polynomial.C μ₂ * ((2560 : K[X]) * p.coeff 0)) := by
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
  have hcore9 :=
    alignedSquareNinth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form
  obtain ⟨s₅, s₆, s₇, s₈, s₉, hd1, hd2, hd3, hd4, hd5, hq1⟩ :=
    alignedSquareNinth_solved_410 hh0 hcore9 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, u, v, s₅, s₆, s₇, s₈, s₉, hp3,
    hDform, hM4, hM6form, hM8form, hM10form, hM12form, hM14form, hv,
    hd1, hd2, hd3, hd4, hd5, hq1⟩

end Max11DegreeRoutes
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Exact nonsquare-chamber ninth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the parity
kill `κ₈ = 0` realized as `M₁₄ ≡ 0`, and the septic-block descent on
the fifth face's divisibility `g² - 4 p₂ = H f` — the FIRST nonsquare
row that does not solve outright: `q₁` is consumed with an
`H`-cofactor inside the explicit quotient. -/
theorem normalized410ScaleTwo_alignedNinthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ : K) (g f : K[X]),
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
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((80 : K[X]) * g *
              ((11 : K[X]) * g ^ 2 - (12 : K[X]) * p.coeff 2) * f ^ 3 +
            (2560 : K[X]) * p.coeff 1 *
              ((7 : K[X]) * g ^ 2 - (4 : K[X]) * p.coeff 2) * f ^ 2 +
            (122880 : K[X]) * p.coeff 1 ^ 2 * g * f +
            (327680 : K[X]) * p.coeff 1 ^ 3 =
          H * (((30720 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (96 : K[X])) * g * f ^ 2 +
            ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * p.coeff 1 * f +
            (1048576 : K[X]) * q.coeff 1 +
            Polynomial.C κ₇ * ((4 : K[X]) * g) +
            Polynomial.C κ₅ * ((512 : K[X]) * p.coeff 1) +
            Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0 * g) -
            (983040 : K[X]) * p.coeff 0 ^ 2 * g -
            Polynomial.C κ *
              ((262144 : K[X]) * p.coeff 0 * p.coeff 1))) := by
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
  have hcore9 :=
    alignedNonsquareNinth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
      hM12form hM140
  have hq1 := alignedNonsquareNinth_solved_410 hH hcore9 hf
  exact ⟨κ, κ₃, κ₅, κ₇, g, f, hg, hD0, hM4, hM60, hM8form, hM100,
    hM12form, hM140, hf, hq1⟩

end Max11DegreeRoutes
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
open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Extended root data of the consumed degree-`4` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order — the deeper kills are in the previous root
packets), and the NEW degree-`4` content splits by chamber.  The square
chamber gains the tie `640 u(a)³ v(a)³ = 7 μ u(a)⁶`, whose clash with
the sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a
factor-`273` mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`, plus `s₅(a) = 0`, the
`s₅`/`s₆` ties, and the `q₁` value tie — the first aligned root tie
seeing `κ₇`.  The nonsquare chamber's septic block dies at `a` and
collapses on the quadratic kill to the PERFECT CUBE
`640 (g(a) f(a) + 8 p₁(a))³ = 0`, forcing the NEW ROOT PIN
`g(a) f(a) + 8 p₁(a) = 0` — the first aligned root pin on `p₁` in the
nonsquare chamber.  `q₁` does NOT vanish and no new vanishing is
claimed; both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedNinthRow_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a : K) (κ : K), H.eval a = 0 ∧
      (8 : K[X]) * q.coeff 8 =
        H * ((15 : K[X]) * p.coeff 3 ^ 2 +
          (20 : K[X]) * p.coeff 2 * H ^ 2 + Polynomial.C κ * H ^ 3) ∧
      (p.coeff 3).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 ∧
      ((∃ (μ μ₂ κ₃ κ₅ κ₇ : K) (h0 u v s₅ s₆ s₉ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (80 : K[X]) * u *
                ((11 : K[X]) * u ^ 2 - (12 : K[X]) * p.coeff 2) *
                v ^ 3 -
              Polynomial.C μ *
                ((273 : K[X]) * u ^ 6 -
                  (2520 : K[X]) * p.coeff 2 * u ^ 4 +
                  (6720 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                  (3584 : K[X]) * p.coeff 2 ^ 3) = h0 * s₅ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (640 : K) * u.eval a ^ 3 * v.eval a ^ 3 =
            (7 : K) * μ * u.eval a ^ 6 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₅.eval a =
            -(15360 : K) * (p.coeff 1).eval a * u.eval a ^ 2 *
              v.eval a ^ 2 ∧
          s₅.eval a = 0 ∧
          s₆.eval a =
            -((5 : K) * μ₂ * u.eval a ^ 4) -
              (896 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 3 -
              (122880 : K) * (p.coeff 1).eval a ^ 2 * u.eval a *
                v.eval a ∧
          (1048576 : K) * (q.coeff 1).eval a =
            s₉.eval a - (4 : K) * κ₇ * u.eval a -
              (512 : K) * κ₅ * (p.coeff 1).eval a -
              (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
              (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
              (262144 : K) * κ * (p.coeff 0).eval a *
                (p.coeff 1).eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (80 : K) * g.eval a *
                  ((11 : K) * g.eval a ^ 2 -
                    (12 : K) * (p.coeff 2).eval a) * f.eval a ^ 3 +
                (2560 : K) * (p.coeff 1).eval a *
                  ((7 : K) * g.eval a ^ 2 -
                    (4 : K) * (p.coeff 2).eval a) * f.eval a ^ 2 +
                (122880 : K) * (p.coeff 1).eval a ^ 2 * g.eval a *
                  f.eval a +
                (327680 : K) * (p.coeff 1).eval a ^ 3 = 0 ∧
            g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a = 0)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  rcases hsource with
    ⟨hH, _hHdeg2, hPdegree, hQdegree, hp4, hq10, hKeller⟩
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
  have hclear := alignedSecondDefect_clearing_410 hM
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    obtain ⟨μ, _hμ2, hDform⟩ :=
      ninthPower_squareChamber_form_410 hH hHsq hrel
    have hdeg1 : h0.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hHsq
      rw [hHdegree, Polynomial.natDegree_pow] at hdegree
      omega
    have hkill0 : ∀ b : K, h0.eval b = 0 → (p.coeff 3).eval b = 0 := by
      intro b hb
      apply alignedThird_rootKill_p3_410 hrel
      rw [hHsq]
      simp only [Polynomial.eval_pow, hb]
      norm_num
    obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
    obtain ⟨u, hu, _hq6⟩ :=
      alignedSquareFourth_descent_410 hh0 hdeg1 hcore
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
    obtain ⟨v, hv, _hq4⟩ :=
      alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
      twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
    have hcore7 :=
      alignedSquareSeventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form
    obtain ⟨s, hs, _hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₈, hM14rel⟩ :=
      alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
      twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
    have hcore9 :=
      alignedSquareNinth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form
    obtain ⟨s₅, s₆, s₇, s₈, s₉, hd1, hd2, hd3, hd4, hd5, hq1⟩ :=
      alignedSquareNinth_solved_410 hh0 hcore9 hv
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hHroot : H.eval a = 0 := by
      rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hHroot
    have hp3d : (p.coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hkilla : u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hv
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hμtie : (80 : K) * u.eval a * v.eval a ^ 3 =
        μ * ((35 : K) * u.eval a ^ 4 -
          (336 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
          (1344 : K) * (p.coeff 2).eval a ^ 2) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hs
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hkilltie : u.eval a *
        ((16 : K) * v.eval a ^ 3 - (7 : K) * μ * u.eval a ^ 3) = 0 := by
      linear_combination (1 / 5 : K) * hμtie -
        (336 / 5 : K) * μ * (p.coeff 2).eval a * hkilla
    have hd1a :
        (80 : K) * u.eval a *
            ((11 : K) * u.eval a ^ 2 -
              (12 : K) * (p.coeff 2).eval a) * v.eval a ^ 3 -
          μ * ((273 : K) * u.eval a ^ 6 -
            (2520 : K) * (p.coeff 2).eval a * u.eval a ^ 4 +
            (6720 : K) * (p.coeff 2).eval a ^ 2 * u.eval a ^ 2 -
            (3584 : K) * (p.coeff 2).eval a ^ 3) = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd1
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hnewtie : (640 : K) * u.eval a ^ 3 * v.eval a ^ 3 =
        (7 : K) * μ * u.eval a ^ 6 := by
      linear_combination hd1a +
        ((896 : K) * μ * (p.coeff 2).eval a ^ 2 -
          (1456 : K) * μ * (p.coeff 2).eval a * u.eval a ^ 2 +
          (266 : K) * μ * u.eval a ^ 4 -
          (240 : K) * u.eval a * v.eval a ^ 3) * hkilla
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h273 : ((273 : K) * μ) * u.eval a ^ 6 = 0 := by
          linear_combination hnewtie - (40 : K) * u.eval a ^ 3 * h16
        have h273μ : (273 : K) * μ = 0 :=
          (mul_eq_zero.mp h273).resolve_right (pow_ne_zero 6 hu)
        have hμ0 : μ = 0 :=
          (mul_eq_zero.mp h273μ).resolve_left (by norm_num)
        have h16v : (16 : K) * v.eval a ^ 3 = 0 := by
          rw [hμ0] at h16
          linear_combination h16
        have hv3 : v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp h16v).resolve_left (by norm_num)
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        exact Or.inr ⟨hv0, hμ0⟩
    have hs5raw : s₅.eval a =
        -(15360 : K) * (p.coeff 1).eval a * u.eval a ^ 2 *
          v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (2560 : K) * (p.coeff 1).eval a * v.eval a ^ 2 * hkilla
    have hs5kill : s₅.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs5raw, hu0]; ring
      · rw [hs5raw, hv0]; ring
    have hs6tie : s₆.eval a =
        -((5 : K) * μ₂ * u.eval a ^ 4) -
          (896 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 3 -
          (122880 : K) * (p.coeff 1).eval a ^ 2 * u.eval a *
            v.eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev +
        ((5376 : K) * μ * (p.coeff 1).eval a * u.eval a -
          (80 : K) * μ₂ * (p.coeff 2).eval a +
          (40 : K) * μ₂ * u.eval a ^ 2) * hkilla
    have hq1tie : (1048576 : K) * (q.coeff 1).eval a =
        s₉.eval a - (4 : K) * κ₇ * u.eval a -
          (512 : K) * κ₅ * (p.coeff 1).eval a -
          (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
          (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
          (262144 : K) * κ * (p.coeff 0).eval a *
            (p.coeff 1).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq1
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, κ₃, κ₅, κ₇, h0, u, v, s₅, s₆, s₉, hh0, hHsq,
        hroot, hp3, hv, hd1, hp3d, hkilla, hnewtie, hdich, hs5raw,
        hs5kill, hs6tie, hq1tie⟩⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    obtain ⟨_hκ₂, hD0⟩ :=
      ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
    have hsimple : ∀ b : K, H.eval b = 0 → H.derivative.eval b ≠ 0 :=
      fun b hb =>
        nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq hb
    have hkill : ∀ b : K, H.eval b = 0 → (p.coeff 3).eval b = 0 :=
      fun b hb => alignedThird_rootKill_p3_410 hrel hb
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
      twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq
        hM14rel
    have hcore9 :=
      alignedNonsquareNinth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
        hM12form hM140
    have hq1 := alignedNonsquareNinth_solved_410 hH hcore9 hf
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hg, Polynomial.eval_mul, hroot, zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hroot
    have hkilla : g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hf
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hbtie : (80 : K) * g.eval a *
          ((11 : K) * g.eval a ^ 2 -
            (12 : K) * (p.coeff 2).eval a) * f.eval a ^ 3 +
        (2560 : K) * (p.coeff 1).eval a *
          ((7 : K) * g.eval a ^ 2 -
            (4 : K) * (p.coeff 2).eval a) * f.eval a ^ 2 +
        (122880 : K) * (p.coeff 1).eval a ^ 2 * g.eval a * f.eval a +
        (327680 : K) * (p.coeff 1).eval a ^ 3 = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq1
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have h640 : (640 : K) *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 := by
      linear_combination hbtie -
        ((80 : K) * f.eval a ^ 2 *
          ((3 : K) * f.eval a * g.eval a +
            (32 : K) * (p.coeff 1).eval a)) * hkilla
    have hcube3 :
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp h640).resolve_left (by norm_num)
    have hpin :
        g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a = 0 :=
      pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hcube3
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hpin⟩⟩

end Max11DegreeRoutes
