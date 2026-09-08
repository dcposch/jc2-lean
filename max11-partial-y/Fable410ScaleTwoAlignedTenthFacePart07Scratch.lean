import Fable410ScaleTwoAlignedTenthFacePart06Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Chamber quotients of the thirty-third-power relation -/

set_option maxHeartbeats 64000000 in
/-- In the square chamber `H = h₀²` the thirty-third-power relation
resolves to the literal half-integral form `D = C μ₅ * h₀³³` with
`μ₅² = c`; the scalar `μ₅` is an honest residual and is not cleared. -/
theorem thirtyThirdPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 33) :
    ∃ μ₅ : K, μ₅ ^ 2 = c ∧ D = Polynomial.C μ₅ * h0 ^ 33 := by
  have hdvd : (h0 ^ 33) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h66 := hrel
    rw [hF, hHsq] at h66
    apply mul_left_cancel₀ (pow_ne_zero 66 hh0)
    linear_combination h66
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₅, hμ₅⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₅, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₅ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₅, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₅]
    ring

#print axioms thirtyThirdPower_squareChamber_form_410

end Max11DegreeRoutes
