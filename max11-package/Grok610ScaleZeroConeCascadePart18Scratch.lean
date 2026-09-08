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

/-- Polynomial pullback of `degreeZeroAlphaGroup610`. -/
def degreeZeroAlphaGroupPolynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (35 / 729 : k) • (A ^ 5 * B) -
    (51 / 729 : k) • (A ^ 4 * D0) -
    (222 / 729 : k) • (A ^ 3 * B * C0) -
    (117 / 729 : k) • (A ^ 2 * B ^ 3) +
    (189 / 729 : k) • (A ^ 2 * B * E0) +
    (297 / 729 : k) • (A ^ 2 * C0 * D0) +
    (324 / 729 : k) • (A * B ^ 2 * D0) +
    (324 / 729 : k) • (A * B * C0 ^ 2) -
    (324 / 729 : k) • (A * D0 * E0) +
    (108 / 729 : k) • (B ^ 3 * C0) -
    (324 / 729 : k) • (B * C0 * E0) -
    (324 / 729 : k) • (B * D0 ^ 2) -
    (324 / 729 : k) • (C0 ^ 2 * D0)

end PrimitivePolynomial610

end Max11DegreeRoutes
