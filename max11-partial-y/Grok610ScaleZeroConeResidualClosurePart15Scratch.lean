import Grok610ScaleZeroConeCascadeScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- Linear `E₀` coefficient of the primitive at `β = 0`. -/
def degreeZeroE0LinearPolynomial610
    (l alpha theta : k) (A B C0 D0 : k[X]) : k[X] :=
  (-(122472 / 2239488 * l : k)) • A ^ 4 -
    (483840 / 2239488 : k) • (A ^ 3 * B) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2) +
    (1658880 / 2239488 : k) • (A * B * C0) +
    (276480 / 2239488 : k) • B ^ 3 -
    (1679616 / 2239488 * l : k) • (B * D0) -
    (839808 / 2239488 * l : k) • C0 ^ 2 -
    (2488320 / 2239488 : k) • (C0 * D0) +
    (189 / 729 * alpha : k) • (A ^ 2 * B) -
    (324 / 729 * alpha : k) • (A * D0) -
    (324 / 729 * alpha : k) • (B * C0) +
    C theta

end ResidualSplittings610

end Max11DegreeRoutes
