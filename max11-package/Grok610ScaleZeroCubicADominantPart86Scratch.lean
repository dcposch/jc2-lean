import Grok610ScaleZeroCubicADominantPart83Scratch
import Grok610ScaleZeroCubicADominantPart84Scratch
import Grok610ScaleZeroCubicADominantPart85Scratch

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
theorem cubicSigmaInner_BCE_identity
    (a b c e : k) :
    ((-1 / 40 : k) * a * b * c ^ 3 + (-1 / 16 : k) * a * b * e ^ 2) * kappaCubicSigmaInnerBCE610 a b c e +
      ((1 / 40 : k) * a * b ^ 2 * c ^ 2 + (-1 / 5 : k) * c ^ 4) * lambdaCubicSigmaInnerBCE610 a b c e +
      ((1 / 16 : k) * a * b ^ 2 * e + (-3 / 5 : k) * c ^ 2 * e) * omicronCubicSigmaInnerBCE610 a b c e =
      c ^ 7 := by
  simp only [kappaCubicSigmaInnerBCE610, lambdaCubicSigmaInnerBCE610, omicronCubicSigmaInnerBCE610]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
