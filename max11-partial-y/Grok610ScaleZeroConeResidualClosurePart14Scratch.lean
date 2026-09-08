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

/-- Primitive at `L = 0`, `B = 0`, `D₀ = 0`, `β = 0`.  The letters
`α, ε, η` drop out. -/
def degreeZeroPrimitive_l0_B0_D00_beta0_610
    (delta zeta theta : k) (A C0 E0 : k[X]) : k[X] :=
  (49 / 5184 * delta : k) • A ^ 5 -
    (360 / 5184 * delta : k) • (A ^ 3 * C0) +
    (720 / 5184 * delta : k) • (A * C0 ^ 2) -
    (7 / 192 * zeta : k) • A ^ 4 +
    (40 / 192 * zeta : k) • (A ^ 2 * C0) -
    (48 / 192 * zeta : k) • C0 ^ 2 +
    (7 / 216 * theta : k) • A ^ 3 -
    (36 / 216 * theta : k) • (A * C0) +
    theta • E0

end ResidualSplittings610

end Max11DegreeRoutes
