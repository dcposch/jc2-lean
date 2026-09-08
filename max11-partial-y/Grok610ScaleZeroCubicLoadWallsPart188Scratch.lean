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

def omicronChamberCD610 (alpha epsilon eta : k) (A C D E : k[X]) : k[X] :=
  (-(5 / 27 : k)) • (C ^ 2 * E)
  + (-(5 / 27 : k)) • (C * D ^ 2)
  + (-(2 / 27 * alpha : k)) • (A * D ^ 2)
  + (-(4 / 81 * alpha : k)) • C ^ 3
  + (2 / 9 * alpha : k) • E ^ 2
  + (-(1 / 9 * epsilon : k)) • C ^ 2
  + (1 / 3 * eta : k) • E

end CubicLoadCDChamber610

end Max11DegreeRoutes
