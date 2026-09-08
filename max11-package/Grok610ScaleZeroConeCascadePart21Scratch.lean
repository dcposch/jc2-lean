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

/-- Beta group with the unique-`E₀` face `E₀²` deleted. -/
def degreeZeroBetaGroupNoE2Polynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (2695 / 559872 : k) • A ^ 6 -
    (23940 / 559872 : k) • (A ^ 4 * C0) -
    (51660 / 559872 : k) • (A ^ 3 * B ^ 2) +
    (21168 / 559872 : k) • (A ^ 3 * E0) +
    (127008 / 559872 : k) • (A ^ 2 * B * D0) +
    (63504 / 559872 : k) • (A ^ 2 * C0 ^ 2) +
    (136080 / 559872 : k) • (A * B ^ 2 * C0) -
    (108864 / 559872 : k) • (A * C0 * E0) -
    (108864 / 559872 : k) • (A * D0 ^ 2) +
    (11340 / 559872 : k) • B ^ 4 -
    (54432 / 559872 : k) • (B ^ 2 * E0) -
    (217728 / 559872 : k) • (B * C0 * D0) -
    (36288 / 559872 : k) • C0 ^ 3

end PrimitivePolynomial610

end Max11DegreeRoutes
