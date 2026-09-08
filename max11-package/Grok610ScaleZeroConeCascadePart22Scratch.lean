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

/-- Polynomial pullback of `degreeZeroDeltaGroup610`. -/
def degreeZeroDeltaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (49 / 5184 : k) • A ^ 5 -
    (360 / 5184 : k) • (A ^ 3 * C0) -
    (600 / 5184 : k) • (A ^ 2 * B ^ 2) +
    (1440 / 5184 : k) • (A * B * D0) +
    (720 / 5184 : k) • (A * C0 ^ 2) +
    (720 / 5184 : k) • (B ^ 2 * C0) -
    (2160 / 5184 : k) • D0 ^ 2

end PrimitivePolynomial610

end Max11DegreeRoutes
