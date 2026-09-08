import Fable610ScaleTwoAlignedNinthFacePart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the nonsquare chamber the odd exponent forces both the constant
and the ninth defect itself to vanish: `κ₈ = 0` and `L ≡ 0`. -/
theorem alignedNonsquareNinth_defect_eq_zero_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : k[X]} {κ κ₈ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hL2 :
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₈ * H ^ 45) :
    κ₈ = 0 ∧
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : k[X] :=
    alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 22) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 44 hH)
    have h44 := hL2
    rw [hG] at h44
    linear_combination h44
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₈ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk8 : κ₈ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk8]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk8, hLzero⟩

end Max11DegreeRoutes
