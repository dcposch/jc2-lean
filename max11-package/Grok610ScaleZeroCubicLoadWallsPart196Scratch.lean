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

/-- On `e = c`, the ο top after the κ relation `e = -(2/5) α c` is
`(4/81) α c³` plus a multiple of the λ inner `3ad² + c³`. -/
theorem cubicChamber_ec_scalar_identity (a c d alpha e : k)
    (hrel : e = -((2 / 5 : k) * alpha * c)) :
    (-(5 / 27 : k)) * c ^ 2 * e
      + (-(2 / 27 * alpha : k)) * a * d ^ 2
      + (-(4 / 81 * alpha : k)) * c ^ 3
    = ((4 / 81 : k) * alpha) * c ^ 3
      + (-(2 / 81 : k) * alpha) * (3 * a * d ^ 2 + c ^ 3) := by
  rw [hrel]
  ring

end CubicLoadCDChamber610

end Max11DegreeRoutes
