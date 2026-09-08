import Fable410ScaleTwoAlignedEighthFacePart06Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- In the square chamber `H = h₀²` the twenty-seventh-power relation
resolves to the literal half-integral form `D = C μ₄ * h₀²⁷` with
`μ₄² = c`; the scalar `μ₄` is an honest residual and is not cleared. -/
theorem twentySeventhPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 27) :
    ∃ μ₄ : K, μ₄ ^ 2 = c ∧ D = Polynomial.C μ₄ * h0 ^ 27 := by
  have hdvd : (h0 ^ 27) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h54 := hrel
    rw [hF, hHsq] at h54
    apply mul_left_cancel₀ (pow_ne_zero 54 hh0)
    linear_combination h54
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₄, hμ₄⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₄, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₄ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₄, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₄]
    ring

end Max11DegreeRoutes
