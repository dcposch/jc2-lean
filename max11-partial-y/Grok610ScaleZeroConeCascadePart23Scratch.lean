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

/-- Polynomial pullback of `degreeZeroEpsilonGroup610`. -/
def degreeZeroEpsilonGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 54 : k)) • (A ^ 3 * B) +
    (9 / 54 : k) • (A ^ 2 * D0) +
    (24 / 54 : k) • (A * B * C0) +
    (4 / 54 : k) • B ^ 3 -
    (36 / 54 : k) • (C0 * D0)

end PrimitivePolynomial610

end Max11DegreeRoutes
