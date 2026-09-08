import Grok610ScaleZeroConeResidualClosurePart14Scratch
import Grok610ScaleZeroConeResidualClosurePart43Scratch

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

theorem degreeZeroPrimitive_l0_B0_D00_delta0_eq_A4_add_rest
    (zeta theta : k) (A C0 E0 : k[X]) :
    degreeZeroPrimitive_l0_B0_D00_beta0_610 0 zeta theta A C0 E0 =
      (-(7 / 192 * zeta : k)) • A ^ 4 +
        degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610 zeta theta A C0
          E0 := by
  simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610,
    degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero, zero_add]
  module

end HighAResidualCone610

end Max11DegreeRoutes
