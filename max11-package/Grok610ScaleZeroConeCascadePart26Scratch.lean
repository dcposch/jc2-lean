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

/-- Polynomial pullback of `degreeZeroThetaGroup610`. -/
def degreeZeroThetaGroupPolynomial610 (A B C0 E0 : k[X]) : k[X] :=
  (7 / 216 : k) • A ^ 3 -
    (36 / 216 : k) • (A * C0) -
    (18 / 216 : k) • B ^ 2 +
    (216 / 216 : k) • E0

end PrimitivePolynomial610

end Max11DegreeRoutes
