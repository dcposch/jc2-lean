import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial pullback of `degreeZeroEtaGroup610`. -/
def degreeZeroEtaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (7 / 36 : k) • (A ^ 2 * B) -
    (12 / 36 : k) • (A * D0) -
    (12 / 36 : k) • (B * C0)

end PrimitivePolynomial610

end Max11DegreeRoutes
