import Fable610ScaleTwoAlignedNinthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Scalar resolution of the tenth-row peeled head at the root against
`e₂(a) = 0` and the `u₂` root product: with `x (v - 3 u x) = 0` and
`v = 0`, the head equation forces the exact tie
`135 s = 92160 x² (81 p - y)²` — the carried `p₂`-block has
perfect-square discriminant. -/
theorem alignedTenthSquareTieResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v y p s m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : v = 0)
    (hhead : 184320 * u ^ 2 * v ^ 2 - 44789760 * u ^ 2 * p * x ^ 2 +
      737280 * u ^ 2 * y * x ^ 2 + 2268 * u * m * x ^ 5 -
      2488320 * v ^ 2 * p + 40960 * v ^ 2 * y +
      604661760 * p ^ 2 * x ^ 2 - 14929920 * p * y * x ^ 2 -
      135 * s + 92160 * y ^ 2 * x ^ 2 = 0) :
    135 * s = 92160 * x ^ 2 * (81 * p - y) ^ 2 := by
  have hux2 : u * x ^ 2 = 0 := by
    linear_combination (-(3 : K)⁻¹) * h1 + ((3 : K)⁻¹ * x) * h2
  have hux : u * x = 0 := by
    rcases mul_eq_zero.mp hux2 with hu | hx2
    · rw [hu, zero_mul]
    · rw [(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2, mul_zero]
  linear_combination -hhead +
    (2268 * m * x ^ 4 - 44789760 * p * u * x + 737280 * u * x * y) *
      hux +
    (-2488320 * p * v + 184320 * u ^ 2 * v + 40960 * v * y) * h2

end Max11DegreeRoutes
