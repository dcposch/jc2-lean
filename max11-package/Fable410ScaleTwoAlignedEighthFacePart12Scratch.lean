import Fable410ScaleTwoAlignedEighthFacePart11Scratch

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
