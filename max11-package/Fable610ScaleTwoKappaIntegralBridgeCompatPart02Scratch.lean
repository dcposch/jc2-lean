import Fable610ScaleTwoTerminalIntegralClosureScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`6` row.  Equivalent to
`W - (7/6) β E - γ D - (5/6) δ C - (2/3) ε B - (1/2) ζ A
- (10/9) B E - (10/9) C D - (4/9) α B C - (7/72) β B² + (5/81) B³
- (4/9) α A D - (7/36) β A C + (10/27) A B C + (5/72) δ A²
+ (5/27) A² D + (4/27) α A² B + (35/1296) β A³ - (20/243) A³ B
- (3/8) L C² - (3/4) L B D - (3/4) L A E + (3/16) L A B²
+ (3/16) L A² C - (3/128) L A⁴`
on the second- through seventh-face integrals. -/
def bridgeThetaResidual610 (L A B C0 D0 E0 P Q R S0 T0 U0 W0 : F) : F :=
  W0 - (7 / 6 : F) * betaResidual610 L A B Q * E0 -
    gammaResidual610 L A B C0 P R * D0 -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * C0 -
    (2 / 3 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * B -
    (1 / 2 : F) * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 * A -
    (10 / 9 : F) * B * E0 - (10 / 9 : F) * C0 * D0 -
    (4 / 9 : F) * alphaResidual610 A P * B * C0 -
    (7 / 72 : F) * betaResidual610 L A B Q * B ^ 2 +
    (5 / 81 : F) * B ^ 3 -
    (4 / 9 : F) * alphaResidual610 A P * A * D0 -
    (7 / 36 : F) * betaResidual610 L A B Q * A * C0 +
    (10 / 27 : F) * A * B * C0 +
    (5 / 72 : F) * deltaResidual610 L A B C0 D0 P Q S0 * A ^ 2 +
    (5 / 27 : F) * A ^ 2 * D0 +
    (4 / 27 : F) * alphaResidual610 A P * A ^ 2 * B +
    (35 / 1296 : F) * betaResidual610 L A B Q * A ^ 3 -
    (20 / 243 : F) * A ^ 3 * B -
    (3 / 8 : F) * L * C0 ^ 2 -
    (3 / 4 : F) * L * B * D0 -
    (3 / 4 : F) * L * A * E0 +
    (3 / 16 : F) * L * A * B ^ 2 +
    (3 / 16 : F) * L * A ^ 2 * C0 -
    (3 / 128 : F) * L * A ^ 4

end BridgeKappaDepression610

end Max11DegreeRoutes
