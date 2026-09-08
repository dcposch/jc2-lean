import Grok610ScaleZeroConeResidualClosurePart29Scratch
import Grok610ScaleZeroConeResidualClosurePart30Scratch
import Grok610ScaleZeroConeResidualClosurePart39Scratch
import Grok610ScaleZeroConeResidualClosurePart24Scratch
import Grok610ScaleZeroConeResidualClosurePart25Scratch
import Grok610ScaleZeroConeResidualClosurePart26Scratch
import Grok610ScaleZeroConeResidualClosurePart27Scratch

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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart24Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart25Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart26Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart27Scratch in
set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
    (alpha delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hD : D0.natDegree = 0)
    (hK : highA_l0_B0_beta0_A5Coefficient610 delta D0 ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hKdeg :
      (highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree = 0 :=
    highA_l0_B0_beta0_A5Coefficient610_natDegree_eq_zero delta hD
  have hlead :
      (A ^ 5 * highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree =
        5 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 5 hA) hK, natDegree_pow, hKdeg, add_zero]
  have hrest :
      (degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610 alpha delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        5 * A.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hDlt, hE⟩
    have hbase :
        (degreeZeroBaseGroup_l0_B0_noA5D0_Rest610 A C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroBaseGroup_l0_B0_noA5D0_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupNoA5Polynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroDeltaGroupNoA5Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610]
    exact natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610 hbase (natDegree_smul_lt610 alpha halpha))
              (natDegree_smul_lt610 delta hdelta))
            (natDegree_smul_lt610 epsilon hepsilon))
          (natDegree_smul_lt610 zeta hzeta))
        (natDegree_smul_lt610 eta heta))
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A5_combined_add_rest,
    highA_l0_B0_beta0_A5_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighAResidualCone610

end Max11DegreeRoutes
