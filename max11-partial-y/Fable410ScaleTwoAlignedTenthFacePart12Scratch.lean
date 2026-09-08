import Fable410ScaleTwoAlignedTenthFacePart11Scratch

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
