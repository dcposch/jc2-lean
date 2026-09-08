import Grok610ScaleZeroCubicLoadWallsPart05Scratch

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

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

/-- Two-face certificate on the CD chamber (CAS: `{3ad²+c³, cd²}`
saturates to `(1)` at `a,c,d ≠ 0`). -/
theorem cubicSigmaInner_CD_chamber_identity (a c d : k) :
    c * lambdaCubicSigmaInnerCD610 a c d
      - (3 * a) * omicronCubicSigmaInnerCD610 c d = c ^ 4 := by
  simp only [lambdaCubicSigmaInnerCD610, omicronCubicSigmaInnerCD610]
  ring

end CubicLoadWallFaces610

end Max11DegreeRoutes
