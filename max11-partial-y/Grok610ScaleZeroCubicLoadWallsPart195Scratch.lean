import Grok610ScaleZeroCubicLoadMultiScratch
import Max11SpeedReflectDegLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronC2Block_of_natDegree_E_eq_zero
    (epsilon : k) (C E : k[X])
    (he0 : E.natDegree = 0) :
    (-(5 / 27 : k)) • (C ^ 2 * E) + (-(1 / 9 * epsilon : k)) • C ^ 2 =
      ((-(5 / 27 : k)) * E.leadingCoeff +
        (-(1 / 9 * epsilon : k))) • C ^ 2 := by
  have hE : E = Polynomial.C E.leadingCoeff := by
    have hcoeff : E.coeff 0 = E.leadingCoeff := by
      rw [← coeff_natDegree, he0]
    rw [← hcoeff]
    exact eq_C_of_natDegree_eq_zero he0
  conv_lhs => rw [hE]
  rw [mul_comm (C ^ 2) (Polynomial.C _), smul_eq_C_mul, smul_eq_C_mul,
    ← mul_assoc, ← C_mul, ← add_mul, ← C_add, ← smul_eq_C_mul]

end CubicLoadCDChamber610

end Max11DegreeRoutes
