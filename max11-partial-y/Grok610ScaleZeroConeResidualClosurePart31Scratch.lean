import Grok610ScaleZeroConeResidualClosurePart14Scratch
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

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart24Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart25Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart26Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart27Scratch in
set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_l0_B0_D00_beta0
    (alpha delta epsilon zeta eta theta : k)
    (A C0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta eta
        theta A 0 C0 0 E0 =
      degreeZeroPrimitive_l0_B0_D00_beta0_610 delta zeta theta A C0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitive_l0_B0_D00_beta0_610,
    degreeZeroBaseGroupPolynomial610, degreeZeroAlphaGroupPolynomial610,
    degreeZeroBetaGroupPolynomial610, degreeZeroDeltaGroupPolynomial610,
    degreeZeroEpsilonGroupPolynomial610, degreeZeroZetaGroupPolynomial610,
    degreeZeroEtaGroupPolynomial610, degreeZeroThetaGroupPolynomial610,
    zero_mul, mul_zero, neg_zero, zero_smul, smul_zero, zero_add,
    add_zero, sub_zero, zero_pow_two, zero_pow_three, zero_pow_four,
    zero_pow_five]
  module

end ResidualSplittings610

end Max11DegreeRoutes
