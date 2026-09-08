import Fable610ScaleTwoAlignedEleventhFacePart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- In the nonsquare chamber the odd exponent forces both the constant
and the eleventh defect to vanish: `κ₁₀ = 0` and `Λ ≡ 0`, exactly as
for `D`, `F`, `I`, and `L`. -/
theorem alignedNonsquareEleventh_defect_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    κ₁₀ = 0 ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
        κ = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 27) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 54 hH)
    have h54 := hL2
    rw [hG] at h54
    linear_combination h54
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₁₀ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk10 : κ₁₀ = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk10]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk10, hLzero⟩

end Max11DegreeRoutes
