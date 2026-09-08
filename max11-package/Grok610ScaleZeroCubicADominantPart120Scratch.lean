import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

def kappaCubicSigmaFaceBCDE610 (A B C D E : k[X]) : k[X] :=
  (5 / 243 : k) • (A * B ^ 3)
  - (5 / 27 : k) • (B * C ^ 2)
  + (10 / 9 : k) • (D * E)

end CubicBalanced610

end Max11DegreeRoutes
