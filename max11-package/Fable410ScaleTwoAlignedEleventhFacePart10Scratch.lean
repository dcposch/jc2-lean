import Fable410ScaleTwoAlignedEleventhFacePart09Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- The consumed degree-`1` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` the row yields a `q`-free block
identity whose `H²`-part carries the tied constant block
`κ₁₁ + 7864320 κ₃ p₀² + 10240 κ₇ p₀ - 838860800 p₀³` — `κ₁₁` is tied
two `H`-levels deep, not solved.  The block collapses at the core
root to the perfect-cube product `102400 g³ (g f + 8 p₁)³`. -/
theorem alignedNonsquareTwelfth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 : K[X]} {κ₃ κ₇ κ₁₁ : K}
    (hH : H ≠ 0)
    (hcore :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
            (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (51200 : K[X]) * H * a1 * g *
            ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
              (432 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
        (((12902400 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 4 -
              Polynomial.C κ₃ * ((40320 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 4) -
              (68812800 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (68812800 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 -
              Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3) -
              (334233600 : K[X]) * a1 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (78643200 : K[X]) * a0 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
          H * ((176947200 : K[X]) * a0 * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (183500800 : K[X]) * a1 ^ 3 * g * (g ^ 2 - (4 : K[X]) * a2) +
              (314572800 : K[X]) * a0 * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2) -
              Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2)) -
              (209715200 : K[X]) * a1 ^ 3 * a2 * g) +
          H ^ 2 * (-(117964800 : K[X]) * a0 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              Polynomial.C κ₇ * ((480 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              (629145600 : K[X]) * a0 * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (314572800 : K[X]) * a0 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) +
              Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              (104857600 : K[X]) * a1 ^ 4 +
              (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
              Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
          H ^ 3 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * g +
              Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g)) +
          H ^ 4 * ((838860800 : K[X]) * a0 ^ 3 -
              Polynomial.C κ₁₁ * ((1 : K[X])) -
              Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
          (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) * f ^ 3 +
      (51200 : K[X]) * a1 * g *
        ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
          (432 : K[X]) * a2 ^ 2) * f ^ 2 +
      (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * f +
      (209715200 : K[X]) * a1 ^ 3 * a2 * g =
      H * (-(334233600 : K[X]) * a1 ^ 2 * a2 * f ^ 2 -
        (183500800 : K[X]) * a1 ^ 3 * g * f +
        (78643200 : K[X]) * a0 * a2 ^ 2 * f ^ 2 +
        (314572800 : K[X]) * a0 * a1 * a2 * g * f -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * f ^ 2) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * f) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) +
      H * (-(68812800 : K[X]) * a1 ^ 2 * f ^ 3 +
          (68812800 : K[X]) * a0 * a2 * f ^ 3 +
          (176947200 : K[X]) * a0 * a1 * g * f ^ 2 +
          (629145600 : K[X]) * a0 * a1 ^ 2 * f -
          (314572800 : K[X]) * a0 ^ 2 * a2 * f -
          (629145600 : K[X]) * a0 ^ 2 * a1 * g +
          Polynomial.C κ₇ * ((1280 : K[X]) * a2 * f) +
          Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) -
          Polynomial.C κ₃ * ((215040 : K[X]) * a2 * f ^ 3) -
          Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * f ^ 2) -
          Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * f) +
          Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * f) +
          Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g) +
        H * ((12902400 : K[X]) * a0 * f ^ 4 -
            (117964800 : K[X]) * a0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) +
            Polynomial.C κ₇ * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * f ^ 2) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2)))) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing twelfth-row packets -/

end Max11DegreeRoutes
