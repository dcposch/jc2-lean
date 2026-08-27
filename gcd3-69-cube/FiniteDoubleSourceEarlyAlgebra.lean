import FiniteDoubleSource

/-! # Early source algebra at a cubic double-root jet

The cubic factor `3 * r * c ^ 3 + A` and the second-order ninth-Faber
residue cannot vanish together on a nonzero double-root jet.
-/

noncomputable section

/-- Characteristic-zero residue contradiction for the early double-root
source pair. -/
theorem GCD369CubeDoubleSourceEarlyAlgebra_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (r A c : K) (hr : r ≠ 0) (_hA : A ≠ 0) (hc : c ≠ 0)
    (hf : 3 * r * c * (3 * r * c ^ 3 + A) = 0)
    (hg : 27 * r ^ 3 * c ^ 6 + (27 / 2) * r ^ 2 * A * c ^ 3 +
      (9 / 8) * r * A ^ 2 = 0) : False := by
  have h3 : (3 : K) ≠ 0 := by norm_num
  have hlin : 3 * r * c ^ 3 + A = 0 := by
    simpa [mul_eq_zero, h3, hr, hc] using hf
  have hAeq : A = -3 * r * c ^ 3 := by
    linear_combination hlin
  rw [hAeq] at hg
  have hval : (-27 / 8 : K) * r ^ 3 * c ^ 6 = 0 := by
    calc
      _ = 27 * r ^ 3 * c ^ 6 +
          (27 / 2) * r ^ 2 * (-3 * r * c ^ 3) * c ^ 3 +
          (9 / 8) * r * (-3 * r * c ^ 3) ^ 2 := by ring
      _ = 0 := hg
  exact (mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))
    (pow_ne_zero 6 hc)) hval

#print axioms GCD369CubeDoubleSourceEarlyAlgebra_inconsistent
