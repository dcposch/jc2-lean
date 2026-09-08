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

section MixedD0E0BetaZero610

variable {k : Type*} [Field k] [CharZero k]

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart24Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart25Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart26Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart27Scratch in
set_option maxHeartbeats 16000000 in
theorem mixedConstABC_beta0_D0_leads_impossible
    (l alpha delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hDpos : 0 < D0.natDegree)
    (hE : E0.natDegree < 2 * D0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (-(829440 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(829440 / 2239488 : k)) • D0 ^ 3).natDegree =
        3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighDRest610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        3 * D0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroBaseGroupHighDRest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        ((0 : k) • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      rw [zero_smul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighDRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      hbetaG
      (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_D3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end MixedD0E0BetaZero610

end Max11DegreeRoutes
