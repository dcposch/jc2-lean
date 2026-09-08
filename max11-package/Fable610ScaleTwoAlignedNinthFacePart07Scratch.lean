import Fable610ScaleTwoAlignedEighthFaceScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Scalar resolution of the ninth-row peeled head against the
eighth-face root product and combined-row cubic: `x (v - 3 u x) = 0`,
`1280 u (3 u x - v)(6 u x - v) + 189 m x⁵ = 0`, and
`276480 u³ x³ - 5120 v³ - 189 m x⁶ = 0` force `v = 0` UNCONDITIONALLY,
refined by `x = 0 ∨ (m = 0 ∧ u = 0)`. -/
theorem alignedNinthSquareResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : 1280 * u * (3 * u * x - v) * (6 * u * x - v) +
      189 * m * x ^ 5 = 0)
    (h9 : 276480 * u ^ 3 * x ^ 3 - 5120 * v ^ 3 - 189 * m * x ^ 6 = 0) :
    v = 0 ∧ (x = 0 ∨ (m = 0 ∧ u = 0)) := by
  rcases mul_eq_zero.mp h1 with hx | hv
  · have h3 : (5120 : K) * v ^ 3 = 0 := by
      rw [hx] at h9
      linear_combination -h9
    have h4 : v ^ 3 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num : (5120 : K) ≠ 0)
    exact ⟨(pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h4,
      Or.inl hx⟩
  · have h5 : (189 : K) * (m * x ^ 5) = 0 := by
      linear_combination h2 + (1280 * u * (6 * u * x - v)) * hv
    have h6 : m * x ^ 5 = 0 :=
      (mul_eq_zero.mp h5).resolve_left (by norm_num : (189 : K) ≠ 0)
    rcases mul_eq_zero.mp h6 with hm | hx5
    · have h7 : (138240 : K) * (u * x) ^ 3 = 0 := by
        linear_combination h9 +
          (5120 * (v ^ 2 + 3 * u * x * v + 9 * u ^ 2 * x ^ 2)) * hv +
          (189 * x ^ 6) * hm
      have h8 : (u * x) ^ 3 = 0 :=
        (mul_eq_zero.mp h7).resolve_left
          (by norm_num : (138240 : K) ≠ 0)
      rcases mul_eq_zero.mp
          ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h8) with
        hu0 | hx0
      · have hv0 : v = 0 := by linear_combination hv + 3 * x * hu0
        exact ⟨hv0, Or.inr ⟨hm, hu0⟩⟩
      · have hv0 : v = 0 := by linear_combination hv + 3 * u * hx0
        exact ⟨hv0, Or.inl hx0⟩
    · have hx0 : x = 0 :=
        (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hx5
      have hv0 : v = 0 := by linear_combination hv + 3 * u * hx0
      exact ⟨hv0, Or.inl hx0⟩

end Max11DegreeRoutes
