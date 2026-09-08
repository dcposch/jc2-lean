import Fable410ScaleTwoAlignedNinthFacePart09Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`3` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` of the fifth face the row does NOT
solve — the octic block
`16 (143 g⁴ - 264 p₂ g² + 48 p₂²) f³ + 15360 p₁ g (3 g² - 4 p₂) f²
+ 245760 p₁² g² f + 655360 p₁³ g` is an exact `H`-multiple of the
explicit quotient, and `q₀` sits in its `H²`-part — the first aligned
letter consumed with an `H²`-cofactor (tied two levels deep, not
solved). -/
theorem alignedNonsquareTenth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 b0 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ : K}
    (hH : H ≠ 0)
    (hcore :
      (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
              (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (15360 : K[X]) * H * a1 * g *
            ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
              (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                g ^ 2 - (61440 : K[X]) * a1 ^ 2) *
              (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (245760 : K[X]) * a1 ^ 2 * g ^ 2 *
              (g ^ 2 - (4 : K[X]) * a2) +
            H * (((983040 : K[X]) * a0 -
                Polynomial.C κ₃ * (3072 : K[X])) *
                g * a1 * (g ^ 2 - (4 : K[X]) * a2) -
              (655360 : K[X]) * a1 ^ 3 * g) +
            H ^ 2 *
              (((3932160 : K[X]) * a0 -
                  Polynomial.C κ₃ * (12288 : K[X])) * a1 ^ 2 +
                (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                  Polynomial.C κ₇ * (4 : K[X]) -
                  (983040 : K[X]) * a0 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2)) +
            H ^ 3 *
              (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
                Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
                Polynomial.C κ₉ - (4194304 : K[X]) * b0)))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * f ^ 3 +
        (15360 : K[X]) * a1 * g *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) * f ^ 2 +
        (245760 : K[X]) * a1 ^ 2 * g ^ 2 * f +
        (655360 : K[X]) * a1 ^ 3 * g =
      H * ((((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
            g ^ 2 - (61440 : K[X]) * a1 ^ 2) * f ^ 2 +
        ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          g * a1 * f +
        ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 +
        H * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            f ^ 3 +
          (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
            Polynomial.C κ₇ * (4 : K[X]) -
            (983040 : K[X]) * a0 ^ 2) * f +
          Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
          Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
          Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing tenth-row packets -/

end Max11DegreeRoutes
