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

/-- Unique-max `A` cone: `A` strictly outranks the other four free letters. -/
def UniqueHighACone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree < A.natDegree ∧
    D0.natDegree < A.natDegree ∧
    E0.natDegree < A.natDegree

end DegreeLemmas610

end Max11DegreeRoutes
