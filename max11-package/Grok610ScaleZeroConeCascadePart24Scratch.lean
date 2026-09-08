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

/-- Polynomial pullback of `degreeZeroZetaGroup610`. -/
def degreeZeroZetaGroupPolynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(7 / 192 : k)) • A ^ 4 +
    (40 / 192 : k) • (A ^ 2 * C0) +
    (48 / 192 : k) • (A * B ^ 2) -
    (96 / 192 : k) • (B * D0) -
    (48 / 192 : k) • C0 ^ 2

end PrimitivePolynomial610

end Max11DegreeRoutes
