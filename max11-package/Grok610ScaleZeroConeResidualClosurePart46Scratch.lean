import Grok610ScaleZeroConeResidualClosurePart31Scratch
import Grok610ScaleZeroConeResidualClosurePart44Scratch
import Grok610ScaleZeroConeResidualClosurePart45Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
    (alpha epsilon zeta eta theta j : k)
    (A C0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha 0 0 epsilon zeta eta
            theta A 0 C0 0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha 0 0 epsilon zeta eta
          theta A 0 C0 0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hApos : 0 < A.natDegree := hcone.1
  have hC : C0.natDegree < A.natDegree := hcone.2.2.1
  have hE : E0.natDegree < A.natDegree := hcone.2.2.2.2
  rw [degreeZeroPrimitivePolynomial610_eq_l0_B0_D00_beta0] at hdeg
  by_cases hzeta : zeta = 0
  · subst hzeta
    by_cases htheta : theta = 0
    · subst htheta
      have hle :
          (degreeZeroPrimitive_l0_B0_D00_beta0_610 0 0 0 A C0 E0).natDegree ≤
            0 := by
        simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610, zero_smul,
          zero_mul, smul_zero, add_zero, sub_zero, zero_add]
        simp [natDegree_zero]
      omega
    · have hc : (7 / 216 * theta : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) htheta
      have hA : A ≠ 0 := by
        intro hA0
        simp [hA0] at hApos
      have hlead :
          ((7 / 216 * theta : k) • A ^ 3).natDegree =
            3 * A.natDegree := by
        rw [natDegree_smul _ hc, natDegree_pow]
      have hrest :
          ((-(36 / 216 * theta : k)) • (A * C0) + theta • E0).natDegree <
            3 * A.natDegree := by
        have hAC :
            ((-(36 / 216 * theta : k)) • (A * C0)).natDegree <
              3 * A.natDegree := by
          compute_degree
          omega
        have hE0 : (theta • E0).natDegree < 3 * A.natDegree := by
          compute_degree
          omega
        exact natDegree_add_lt610 hAC hE0
      rw [degreeZeroPrimitive_l0_B0_D00_delta0_zeta0_eq_A3_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hdeg
      omega
  · have hc : (-(7 / 192 * zeta : k)) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hzeta)
    have hA : A ≠ 0 := by
      intro hA0
      simp [hA0] at hApos
    have hlead :
        ((-(7 / 192 * zeta : k)) • A ^ 4).natDegree =
          4 * A.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest :
        (degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610 zeta theta A C0
            E0).natDegree <
          4 * A.natDegree := by
      simp only [degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610]
      compute_degree
      omega
    rw [degreeZeroPrimitive_l0_B0_D00_delta0_eq_A4_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
    omega

end HighAResidualCone610

end Max11DegreeRoutes
