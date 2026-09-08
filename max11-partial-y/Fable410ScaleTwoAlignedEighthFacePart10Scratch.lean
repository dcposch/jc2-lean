import Fable410ScaleTwoAlignedEighthFacePart09Scratch

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
