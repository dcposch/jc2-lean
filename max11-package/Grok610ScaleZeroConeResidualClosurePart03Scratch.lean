import Grok610ScaleZeroConeCascadeScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `E₀` cone. -/
def UniqueHighE0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree < E0.natDegree ∧
    B.natDegree < E0.natDegree ∧
    C0.natDegree < E0.natDegree ∧
    D0.natDegree < E0.natDegree

end ExtraCones610

end Max11DegreeRoutes
