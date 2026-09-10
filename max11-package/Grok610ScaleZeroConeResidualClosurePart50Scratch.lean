import Grok610ScaleZeroConeResidualClosurePart04Scratch
import Grok610ScaleZeroConeResidualClosurePart21Scratch
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

section HighBA6BCone610

variable {k : Type*} [Field k] [CharZero k]

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart24Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart25Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart26Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart27Scratch in
set_option maxHeartbeats 64000000 in
theorem uniqueHighB_impossible_of_A6B_leads
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : A6BLeadsHighBCone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hAB⟩
  have hAne : A ≠ 0 := by
    intro hA0
    simp [hA0, natDegree_zero] at hAB
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(62720 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(62720 / 2239488 : k)) • (A ^ 6 * B)).natDegree =
        6 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 6 hAne) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveNoA6B610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        6 * A.natDegree + B.natDegree := by
    have hA7 :
        ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree <
          6 * A.natDegree + B.natDegree := by
      compute_degree
      omega
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBaseGroupHighA_noA6B_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htail :
        (degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroPrimitiveHighA_noA6B_Rest610]
      exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
        (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
        (natDegree_smul_lt610 epsilon hepsilon)
        (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
        (natDegree_smul_lt610 theta htheta)
    simp only [degreeZeroPrimitiveNoA6B610]
    exact natDegree_add_lt610 hA7 htail
  rw [degreeZeroPrimitivePolynomial610_eq_A6B_add_noA6B_withA7,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBA6BCone610

end Max11DegreeRoutes
