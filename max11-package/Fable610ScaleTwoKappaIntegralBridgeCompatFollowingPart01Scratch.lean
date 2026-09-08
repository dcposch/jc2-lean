import Fable610ScaleTwoKappaIntegralBridgeCompatNextScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`2` row.  Equivalent to
`(1/6) C θ - (1/24) A² θ + (1/3) D η - (1/6) A B η + ...` on the
second- through ninth-face integrals; unlike every lower bridge
residual its derivative is not a pure multiple of its own row — the
degree-`2` and degree-`4` rows are inseparably tied through the
non-constant multiplier `A/12`. -/
def bridgeMuResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  -(1 / 24 : F) * A ^ 2 * bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0
    + (1 / 6 : F) * C0 * bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0
    - (1 / 6 : F) * A * B * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0
    + (1 / 3 : F) * D0 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0
    + (1 / 24 : F) * A ^ 3 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
    - (1 / 6 : F) * A * C0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
    - (1 / 8 : F) * B ^ 2 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
    + (1 / 2 : F) * E0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
    + (1 / 9 : F) * A ^ 2 * B * epsilonResidual610 L A B C0 D0 E0 P Q R T0
    - (1 / 9 : F) * A * D0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0
    - (2 / 9 : F) * B * C0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0
    - (35 / 3456 : F) * A ^ 4 * deltaResidual610 L A B C0 D0 P Q S0
    + (25 / 432 : F) * A ^ 2 * C0 * deltaResidual610 L A B C0 D0 P Q S0
    + (5 / 72 : F) * A * B ^ 2 * deltaResidual610 L A B C0 D0 P Q S0
    - (5 / 36 : F) * B * D0 * deltaResidual610 L A B C0 D0 P Q S0
    - (5 / 72 : F) * C0 ^ 2 * deltaResidual610 L A B C0 D0 P Q S0
    - (77 / 15552 : F) * A ^ 5 * betaResidual610 L A B Q
    + (35 / 972 : F) * A ^ 3 * C0 * betaResidual610 L A B Q
    + (35 / 576 : F) * A ^ 2 * B ^ 2 * betaResidual610 L A B Q
    - (7 / 144 : F) * A ^ 2 * E0 * betaResidual610 L A B Q
    - (7 / 54 : F) * A * B * D0 * betaResidual610 L A B Q
    - (7 / 108 : F) * A * C0 ^ 2 * betaResidual610 L A B Q
    - (35 / 432 : F) * B ^ 2 * C0 * betaResidual610 L A B Q
    + (7 / 36 : F) * C0 * E0 * betaResidual610 L A B Q
    + (7 / 72 : F) * D0 ^ 2 * betaResidual610 L A B Q
    - (10 / 243 : F) * A ^ 4 * B * alphaResidual610 A P
    + (14 / 243 : F) * A ^ 3 * D0 * alphaResidual610 A P
    + (16 / 81 : F) * A ^ 2 * B * C0 * alphaResidual610 A P
    + (2 / 27 : F) * A * B ^ 3 * alphaResidual610 A P
    - (2 / 9 : F) * A * B * E0 * alphaResidual610 A P
    - (2 / 9 : F) * A * C0 * D0 * alphaResidual610 A P
    - (4 / 27 : F) * B ^ 2 * D0 * alphaResidual610 A P
    - (4 / 27 : F) * B * C0 ^ 2 * alphaResidual610 A P
    + (4 / 9 : F) * D0 * E0 * alphaResidual610 A P
    + (5 / 1024 : F) * L * A ^ 6
    + (35 / 1458 : F) * A ^ 5 * B
    - (11 / 256 : F) * L * A ^ 4 * C0
    - (25 / 729 : F) * A ^ 4 * D0
    - (3 / 32 : F) * L * A ^ 3 * B ^ 2
    - (110 / 729 : F) * A ^ 3 * B * C0
    + (1 / 16 : F) * L * A ^ 3 * E0
    - (20 / 243 : F) * A ^ 2 * B ^ 3
    + (7 / 32 : F) * L * A ^ 2 * B * D0
    + (5 / 27 : F) * A ^ 2 * B * E0
    + (7 / 64 : F) * L * A ^ 2 * C0 ^ 2
    + (5 / 27 : F) * A ^ 2 * C0 * D0
    + (1 / 4 : F) * L * A * B ^ 2 * C0
    + (35 / 162 : F) * A * B ^ 2 * D0
    + (35 / 162 : F) * A * B * C0 ^ 2
    - (1 / 4 : F) * L * A * C0 * E0
    - (1 / 8 : F) * L * A * D0 ^ 2
    - (5 / 27 : F) * A * D0 * E0
    + (3 / 128 : F) * L * B ^ 4
    + (20 / 243 : F) * B ^ 3 * C0
    - (3 / 16 : F) * L * B ^ 2 * E0
    - (3 / 8 : F) * L * B * C0 * D0
    - (10 / 27 : F) * B * C0 * E0
    - (5 / 27 : F) * B * D0 ^ 2
    - (1 / 16 : F) * L * C0 ^ 3
    - (5 / 27 : F) * C0 ^ 2 * D0
    + (3 / 8 : F) * L * E0 ^ 2

end BridgeMuDepression610

end Max11DegreeRoutes
