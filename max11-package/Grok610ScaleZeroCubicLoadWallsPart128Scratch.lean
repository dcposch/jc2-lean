import Grok610ScaleZeroCubicLoadWallsPart126Scratch
import Grok610ScaleZeroCubicLoadWallsPart127Scratch

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

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

def degreeZeroN2CubicBCDEWallZetaRest610 (alpha epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk0 alpha epsilon zeta eta theta A B C D E) +
  (degreeZeroN2CubicBCDEWallZetaRest610_chunk1 alpha epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
