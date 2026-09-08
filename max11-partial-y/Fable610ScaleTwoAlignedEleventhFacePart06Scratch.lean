import Fable610ScaleTwoAlignedEleventhFacePart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the square chamber the squared weight-`55/2` integral has a
polynomial square root: `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`.  The constant
`μ₄` is preserved, not cleared. -/
theorem alignedSquareEleventh_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    ∃ μ₄ : K, μ₄ ^ 2 = κ₁₀ ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ =
        Polynomial.C μ₄ * h0 ^ 55 := by
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 55) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ := by
    have h110 := hL2
    rw [hG, hHsq] at h110
    apply mul_left_cancel₀ (pow_ne_zero 110 hh0)
    linear_combination h110
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₁₀
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₄, hμ⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨μ₄, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₄ ^ 2) = Polynomial.C κ₁₀ := by
      rw [Polynomial.C_pow, hμ, hG2]
    exact Polynomial.C_injective hCμ
  · rw [hG, ← hμ]
    ring

end Max11DegreeRoutes
