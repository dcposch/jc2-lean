import Grok610ScaleZeroConeCascadeScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive at `L = 0`, `B = 0`, `D₀ = 0`, `β = 0`, `δ = 0` with the
face `A⁴` deleted. -/
def degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610
    (zeta theta : k) (A C0 E0 : k[X]) : k[X] :=
  (40 / 192 * zeta : k) • (A ^ 2 * C0) -
    (48 / 192 * zeta : k) • C0 ^ 2 +
    (7 / 216 * theta : k) • A ^ 3 -
    (36 / 216 * theta : k) • (A * C0) +
    theta • E0

end HighAResidualCone610

end Max11DegreeRoutes
