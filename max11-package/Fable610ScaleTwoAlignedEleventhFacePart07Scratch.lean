import Fable610ScaleTwoAlignedTenthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Scalar resolution of the eleventh-row peeled head at the root
against `e₂(a) = 0`, the `u₂` root product, and the carried tenth-face
tie `135 s = 92160 x² (81 p - y)²`: the head equation forces the exact
vanishing `t = 0` of the new μ-loaded witness. -/
theorem alignedEleventhSquareTieResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v y p s t m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : v = 0)
    (htie : 135 * s = 92160 * x ^ 2 * (81 * p - y) ^ 2)
    (hhead : -61931520 * u ^ 4 * x ^ 3 + 1433272320 * u ^ 2 * p * x ^ 3 -
      22118400 * u ^ 2 * y * x ^ 3 + 655360 * u * v ^ 3 - 21168 * u * m *
      x ^ 6 - 9674588160 * p ^ 2 * x ^ 3 + 238878720 * p * y * x ^ 3 +
      2160 * s * x + 1215 * t - 1474560 * y ^ 2 * x ^ 3 = 0) :
    t = 0 := by
  have hux2 : u * x ^ 2 = 0 := by
    linear_combination (-(3 : K)⁻¹) * h1 + ((3 : K)⁻¹ * x) * h2
  have hux : u * x = 0 := by
    rcases mul_eq_zero.mp hux2 with hu | hx2
    · rw [hu, zero_mul]
    · rw [(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2, mul_zero]
  linear_combination ((1215 : K)⁻¹) * hhead -
    ((1215 : K)⁻¹ * 16 * x) * htie +
    ((1215 : K)⁻¹ * (21168 * m * x ^ 5 - 1433272320 * p * u * x ^ 2 +
      61931520 * u ^ 3 * x ^ 2 + 22118400 * u * x ^ 2 * y)) * hux -
    ((1215 : K)⁻¹ * 655360 * u * v ^ 2) * h2

end Max11DegreeRoutes
