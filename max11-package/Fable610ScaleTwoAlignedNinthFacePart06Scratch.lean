import Fable610ScaleTwoAlignedNinthFacePart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the square chamber the squared weight-`45/2` integral has a
polynomial square root: `L = μ₃ h₀⁴⁵` with `μ₃² = κ₈`.  The constant
`μ₃` is preserved, not cleared. -/
theorem alignedSquareNinth_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₈ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 :
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₈ * H ^ 45) :
    ∃ μ₃ : K, μ₃ ^ 2 = κ₈ ∧
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ =
        Polynomial.C μ₃ * h0 ^ 45 := by
  set L : K[X] :=
    alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 45) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ := by
    have h90 := hL2
    rw [hG, hHsq] at h90
    apply mul_left_cancel₀ (pow_ne_zero 90 hh0)
    linear_combination h90
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₈
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₃, hμ⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨μ₃, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₃ ^ 2) = Polynomial.C κ₈ := by
      rw [Polynomial.C_pow, hμ, hG2]
    exact Polynomial.C_injective hCμ
  · rw [hG, ← hμ]
    ring

end Max11DegreeRoutes
