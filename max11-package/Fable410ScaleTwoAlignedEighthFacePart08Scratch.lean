import Fable410ScaleTwoAlignedEighthFacePart07Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Parity kill in the nonsquare chamber: the odd exponent of the
twenty-seventh-power relation forces its constant to vanish, and with
it the whole ninth defect. -/
theorem twentySeventhPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 27) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 13) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 26 hH)
    have h26 := hrel
    rw [hG] at h26
    linear_combination h26
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C c := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hc : c = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [ha, zero_mul] at hev
    exact hev.symm
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

/-! ## Square chamber -/

end Max11DegreeRoutes
