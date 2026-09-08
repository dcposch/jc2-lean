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

/-- Base group at `L = 0`, `B = 0` with `A⁵ D₀` deleted. -/
def degreeZeroBaseGroup_l0_B0_noA5D0_Rest610
    (A C0 D0 E0 : k[X]) : k[X] :=
  (-(668160 / 2239488 : k)) • (A ^ 3 * C0 * D0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

end ResidualSplittings610

end Max11DegreeRoutes
