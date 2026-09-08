import Fable410ScaleTwoAlignedTenthFacePart09Scratch

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
