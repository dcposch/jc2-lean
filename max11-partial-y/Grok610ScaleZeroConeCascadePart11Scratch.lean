import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section DegreeLemmas610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `B` cone. -/
def UniqueHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    A.natDegree < B.natDegree ∧
    C0.natDegree < B.natDegree ∧
    D0.natDegree < B.natDegree ∧
    E0.natDegree < B.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
