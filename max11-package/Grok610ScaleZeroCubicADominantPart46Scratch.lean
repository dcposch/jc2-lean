import Grok610ScaleZeroCubicADominantPart44Scratch
import Grok610ScaleZeroCubicADominantPart45Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BC_identity
    (a b c : k) :
    ((-1 / 40 : k) * a * b * c) * kappaCubicSigmaInnerBC610 a b c +
      ((1 / 40 : k) * a * b ^ 2 + (-1 / 5 : k) * c ^ 2) * lambdaCubicSigmaInnerBC610 a b c =
      c ^ 5 := by
  simp only [kappaCubicSigmaInnerBC610, lambdaCubicSigmaInnerBC610]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
