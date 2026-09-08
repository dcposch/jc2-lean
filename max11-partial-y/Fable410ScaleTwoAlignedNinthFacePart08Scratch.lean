import Fable410ScaleTwoAlignedNinthFacePart07Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`3` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains `h₀³`,
and the peel is SEVEN deep: the NEW μ-loaded septic divisibility
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
+ 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀` — self-similar to the sixth-,
seventh-, and eighth-face divisibilities one level down — then the
explicit peels producing `s₁₁` through `s₁₆` (`s₁₅` is the first peel
letter loaded with `μ₄`), and the solved row with NO `h₀`-suppressed
tail: `q₀` carries no `h₀` factor and `κ₉` enters at level zero. -/
theorem alignedSquareTenth_solved_410 {K : Type*} [Field K] [CharZero K]
    {h0 u v a0 a1 a2 b0 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
              (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (15360 : K[X]) * h0 ^ 2 * a1 * u *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
                (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
                (17920 : K[X]) * a2 ^ 3 * u) +
            h0 * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                  u ^ 2 - (61440 : K[X]) * a1 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (245760 : K[X]) * a1 ^ 2 * u ^ 2 *
                (u ^ 2 - (4 : K[X]) * a2)) +
            h0 ^ 2 *
              (Polynomial.C μ *
                  (a1 * ((10080 : K[X]) * u ^ 4 -
                    (53760 : K[X]) * a2 * u ^ 2 +
                    (43008 : K[X]) * a2 ^ 2)) +
                Polynomial.C μ₂ *
                  (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
                    (960 : K[X]) * a2 ^ 2))) +
            h0 ^ 3 *
              (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                  a1 * u * (u ^ 2 - (4 : K[X]) * a2) -
                (655360 : K[X]) * a1 ^ 3 * u) +
            h0 ^ 4 *
              (Polynomial.C μ *
                  ((86016 : K[X]) * a0 * a2 * u -
                    (17920 : K[X]) * a0 * u ^ 3 +
                    (43008 : K[X]) * a1 ^ 2 * u) +
                Polynomial.C μ₂ *
                  ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
                Polynomial.C μ₃ *
                  ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3)) +
            h0 ^ 5 *
              (((3932160 : K[X]) * a0 -
                  Polynomial.C κ₃ * (12288 : K[X])) * a1 ^ 2 +
                (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                  Polynomial.C κ₇ * (4 : K[X]) -
                  (983040 : K[X]) * a0 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2)) -
            h0 ^ 6 *
              (Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
                Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
                Polynomial.C μ₃ * ((96 : K[X]) * a1) +
                Polynomial.C μ₄ * u) +
            h0 ^ 7 *
              (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
                Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
                Polynomial.C κ₉ - (4194304 : K[X]) * b0)))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₁₀ s₁₁ s₁₂ s₁₃ s₁₄ s₁₅ s₁₆ : K[X],
      (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * v ^ 3 -
          Polynomial.C μ *
            ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
              (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
              (17920 : K[X]) * a2 ^ 3 * u) = h0 * s₁₀ ∧
      s₁₀ + (15360 : K[X]) * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 = h0 * s₁₁ ∧
      s₁₁ + (245760 : K[X]) * a1 ^ 2 * u ^ 2 * v -
          Polynomial.C μ *
            (a1 * ((10080 : K[X]) * u ^ 4 - (53760 : K[X]) * a2 * u ^ 2 +
              (43008 : K[X]) * a2 ^ 2)) -
          Polynomial.C μ₂ *
            (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
              (960 : K[X]) * a2 ^ 2)) = h0 * s₁₂ ∧
      s₁₂ - (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
            u ^ 2 - (61440 : K[X]) * a1 ^ 2) * v ^ 2 +
          (655360 : K[X]) * a1 ^ 3 * u = h0 * s₁₃ ∧
      s₁₃ - ((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            v ^ 3 -
          ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            a1 * u * v -
          Polynomial.C μ *
            ((86016 : K[X]) * a0 * a2 * u - (17920 : K[X]) * a0 * u ^ 3 +
              (43008 : K[X]) * a1 ^ 2 * u) -
          Polynomial.C μ₂ *
            ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) -
          Polynomial.C μ₃ *
            ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3) = h0 * s₁₄ ∧
      s₁₄ - ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 = h0 * s₁₅ ∧
      s₁₅ - (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
            Polynomial.C κ₇ * (4 : K[X]) -
            (983040 : K[X]) * a0 ^ 2) * v +
          Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
          Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
          Polynomial.C μ₃ * ((96 : K[X]) * a1) +
          Polynomial.C μ₄ * u = h0 * s₁₆ ∧
      (4194304 : K[X]) * b0 =
        Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
          Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
          Polynomial.C κ₉ - s₁₆ := by
  obtain ⟨s₁₆, hs₁₆⟩ : ∃ w : K[X],
      w = Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
        Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
        Polynomial.C κ₉ - (4194304 : K[X]) * b0 := ⟨_, rfl⟩
  obtain ⟨s₁₅, hs₁₅⟩ : ∃ w : K[X],
      w = (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
          Polynomial.C κ₇ * (4 : K[X]) - (983040 : K[X]) * a0 ^ 2) * v -
        Polynomial.C μ * ((344064 : K[X]) * a0 * a1) -
        Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) -
        Polynomial.C μ₃ * ((96 : K[X]) * a1) -
        Polynomial.C μ₄ * u + h0 * s₁₆ := ⟨_, rfl⟩
  obtain ⟨s₁₄, hs₁₄⟩ : ∃ w : K[X],
      w = ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 + h0 * s₁₅ := ⟨_, rfl⟩
  obtain ⟨s₁₃, hs₁₃⟩ : ∃ w : K[X],
      w = ((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) * v ^ 3 +
        ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          a1 * u * v +
        Polynomial.C μ *
          ((86016 : K[X]) * a0 * a2 * u - (17920 : K[X]) * a0 * u ^ 3 +
            (43008 : K[X]) * a1 ^ 2 * u) +
        Polynomial.C μ₂ *
          ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
        Polynomial.C μ₃ * ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3) +
        h0 * s₁₄ := ⟨_, rfl⟩
  obtain ⟨s₁₂, hs₁₂⟩ : ∃ w : K[X],
      w = (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
          u ^ 2 - (61440 : K[X]) * a1 ^ 2) * v ^ 2 -
        (655360 : K[X]) * a1 ^ 3 * u + h0 * s₁₃ := ⟨_, rfl⟩
  obtain ⟨s₁₁, hs₁₁⟩ : ∃ w : K[X],
      w = -(245760 : K[X]) * a1 ^ 2 * u ^ 2 * v +
        Polynomial.C μ *
          (a1 * ((10080 : K[X]) * u ^ 4 - (53760 : K[X]) * a2 * u ^ 2 +
            (43008 : K[X]) * a2 ^ 2)) +
        Polynomial.C μ₂ *
          (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
            (960 : K[X]) * a2 ^ 2)) + h0 * s₁₂ := ⟨_, rfl⟩
  obtain ⟨s₁₀, hs₁₀⟩ : ∃ w : K[X],
      w = -(15360 : K[X]) * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 +
        h0 * s₁₁ := ⟨_, rfl⟩
  refine ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs₁₀, hs₁₁, hs₁₂, hs₁₃, hs₁₄, hs₁₅, hs₁₆]
    linear_combination hcore
  · rw [hs₁₀]
    ring
  · rw [hs₁₁]
    ring
  · rw [hs₁₂]
    ring
  · rw [hs₁₃]
    ring
  · rw [hs₁₄]
    ring
  · rw [hs₁₅]
    ring
  · rw [hs₁₆]
    ring

/-! ## Nonsquare chamber -/

end Max11DegreeRoutes
