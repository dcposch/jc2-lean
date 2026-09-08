import Grok610ScaleZeroCubicLoadWallsPart16Scratch
import Grok610ScaleZeroCubicLoadWallsPart17Scratch

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

def degreeZeroN1CubicCDWallBetaRest610 (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X] :=
  (degreeZeroN1CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) +
  (degreeZeroN1CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)

end CubicLoadWallRests610

end Max11DegreeRoutes
