import Grok610ScaleZeroConeResidualClosurePart32Scratch
import Grok610ScaleZeroConeResidualClosurePart33Scratch
import Grok610ScaleZeroConeResidualClosurePart36Scratch
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

section UniqueE0BetaZero610

variable {k : Type*} [Field k] [CharZero k]

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart24Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart25Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart26Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart27Scratch in
set_option maxHeartbeats 16000000 in
theorem uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two
    (l alpha delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hEpos : 1 < E0.natDegree)
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
  rw [degreeZeroPrimitivePolynomial610_eq_e0Terms_add,
    degreeZeroE0Terms610_eq_linear_mul] at hdeg
  have hlin :
      (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0).natDegree ≤
        0 := by
    simp only [degreeZeroE0LinearPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
    compute_degree
    omega
  have hfree :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 0).natDegree ≤
        0 := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroBaseGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitivePolynomial610]
    exact natDegree_add8_le610 hbase
      (natDegree_smul_le_of_le610 alpha halpha)
      (natDegree_smul_le_of_le610 (0 : k) hbetaG)
      (natDegree_smul_le_of_le610 delta hdelta)
      (natDegree_smul_le_of_le610 epsilon hepsilon)
      (natDegree_smul_le_of_le610 zeta hzeta)
      (natDegree_smul_le_of_le610 eta heta)
      (natDegree_smul_le_of_le610 theta htheta)
  by_cases hL : degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 = 0
  · rw [hL, zero_mul, zero_add] at hdeg
    omega
  · have hEne : E0 ≠ 0 := by
      intro hE0
      simp [hE0] at hEpos
    have hLdeg :
        (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0).natDegree =
          0 :=
      natDegree_eq_zero_of_le_zero610 hlin
    have hlead :
        (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 * E0).natDegree =
          E0.natDegree := by
      rw [natDegree_mul hL hEne, hLdeg, zero_add]
    have hrest :
        (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
            theta A B C0 D0 0).natDegree <
          E0.natDegree :=
      hfree.trans_lt (Nat.zero_lt_of_lt hEpos)
    rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
    omega

end UniqueE0BetaZero610

end Max11DegreeRoutes
