import Grok610ScaleZeroConeCascadePart11Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

/-- Extreme high-`B` subcone on which `B⁵` outranks `A⁶ B` and `A⁷`. -/
def ExtremeHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    3 * A.natDegree < 2 * B.natDegree ∧
    7 * A.natDegree < 5 * B.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
