import Grok610ScaleZeroCubicLoadWallsPart186Scratch

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

theorem kappaChamberCD610_of_E_eq_zero (alpha epsilon : k) (C D : k[X]) :
    kappaChamberCD610 alpha epsilon C D 0 =
      (4 / 9 * alpha : k) • (C * D) + (2 / 3 * epsilon : k) • D := by
  simp only [kappaChamberCD610, mul_zero, smul_zero, add_zero, zero_add]

end CubicLoadCDChamber610

end Max11DegreeRoutes
