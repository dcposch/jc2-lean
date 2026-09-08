import Grok610ScaleZeroCubicLoadWallsPart193Scratch

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

theorem omicronChamberCD610_of_alpha_eq_zero_E_eq_zero
    (epsilon eta : k) (A C D : k[X]) :
    omicronChamberCD610 0 epsilon eta A C D 0 =
      (-(5 / 27 : k)) • (C * D ^ 2) +
        (-(1 / 9 * epsilon : k)) • C ^ 2 := by
  rw [omicronChamberCD610_of_alpha_eq_zero]
  have hC2E : (-(5 / 27 : k)) • (C ^ 2 * (0 : k[X])) = 0 := by
    simp
  have hE : ((1 / 3 * eta : k)) • (0 : k[X]) = 0 := by simp
  rw [hC2E, hE]
  abel

end CubicLoadCDChamber610

end Max11DegreeRoutes
