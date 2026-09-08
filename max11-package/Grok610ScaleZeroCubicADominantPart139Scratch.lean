import Grok610ScaleZeroCubicADominantPart135Scratch
import Grok610ScaleZeroCubicADominantPart136Scratch
import Grok610ScaleZeroCubicADominantPart137Scratch
import Grok610ScaleZeroCubicADominantPart138Scratch

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

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BCDE_identity (a b c d e : k) :
    ((1 / 324 : k) * a * b * c ^ 2 * e + (1 / 972 : k) * a * c ^ 3 * d + (1 / 162 : k) * a * d * e ^ 2) * kappaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 324 : k) * a * b ^ 2 * c * e + (1 / 324 : k) * a * b * c ^ 2 * d + (1 / 9 : k) * e ^ 3) * lambdaCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 72 : k) * a * b * d * e + (1 / 216 : k) * a * c * d ^ 2 + (-1 / 27 : k) * c * e ^ 2) * omicronCubicSigmaInnerBCDE610 a b c d e +
      ((-1 / 243 : k) * a * b * c ^ 3 + (5 / 648 : k) * a * b * e ^ 2 + (1 / 72 : k) * a * c * d * e) * n1CubicSigmaInnerBCDE610 a b c d e =
      e ^ 5 := by
  simp only [kappaCubicSigmaInnerBCDE610, lambdaCubicSigmaInnerBCDE610,
    omicronCubicSigmaInnerBCDE610, n1CubicSigmaInnerBCDE610]
  ring

end CubicBalanced610

end Max11DegreeRoutes
