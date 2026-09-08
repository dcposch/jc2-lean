import Grok610DegreeZeroSourceWrapperScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section LinearDvdAndPoleFive610

variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem linearPolynomial_dvd_of_eval_eq_zero_610
    (h f : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) (hf : f.eval a = 0) : h ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h = C c * (X - C a) := by
    calc
      h = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

end LinearDvdAndPoleFive610

end Max11DegreeRoutes
