import Grok610ScaleZeroCubicLoadConesScratch
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

section CubicLoadSigmaCDFinish610

variable {k : Type*} [Field k] [CharZero k]

/-- Substituted λ-rest on the CD chamber after `B = 0` and odd loads vanish. -/
def lambdaChamberRestCD610
    (alpha epsilon eta : k) (A C D E : k[X]) : k[X] :=
  (5 / 9 : k) • E ^ 2
  + (4 / 9 * alpha : k) • (C * E)
  + (2 / 9 * alpha : k) • D ^ 2
  + (2 / 3 * epsilon : k) • E
  + (1 / 3 * eta : k) • C

end CubicLoadSigmaCDFinish610

end Max11DegreeRoutes
