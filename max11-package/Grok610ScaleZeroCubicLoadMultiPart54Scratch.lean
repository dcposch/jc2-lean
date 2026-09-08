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

section CubicLoadMultiAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Convert a specialised non-strict band into a strict band or an
equality wall. -/
theorem band_lt_or_eq_of_le {n m : ℕ} (h : n ≤ m) : n < m ∨ n = m :=
  lt_or_eq_of_le h

end CubicLoadMultiAssembly610

end Max11DegreeRoutes
