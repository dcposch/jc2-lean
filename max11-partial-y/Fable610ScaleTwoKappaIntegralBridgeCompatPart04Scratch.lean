import Fable610ScaleTwoKappaIntegralBridgeCompatPart02Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`4` row.  Equivalent to
`(1/6) A θ + (1/3) B η + (1/2) C ζ - (1/8) A² ζ + (2/3) D ε
- (2/9) A B ε + (5/6) E δ + (35/1296) A³ δ - (5/36) A C δ
- (5/72) B² δ + (20/243) A³ B α - (4/27) A² D α - (8/27) A B C α
- (4/81) B³ α + (4/9) B E α + (4/9) C D α + (385/31104) A⁴ β
- (35/432) A² C β - (35/432) A B² β + (7/36) A E β + (7/36) B D β
+ (7/72) C² β - (3/256) L A⁵ + (3/32) L A³ C + (9/64) L A² B²
- (3/16) L A² E - (3/8) L A B D - (3/16) L A C² - (3/16) L B² C
+ (3/4) L C E + (3/8) L D² - (35/729) A⁴ B + (20/243) A³ D
+ (20/81) A² B C + (20/243) A B³ - (10/27) A B E - (10/27) A C D
- (5/27) B² D - (5/27) B C² + (10/9) D E`
on the second- through ninth-face integrals. -/
def bridgeKappaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 6 : F) * A * bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 +
    (1 / 3 : F) * B * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 +
    (1 / 2 : F) * C0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 -
    (1 / 8 : F) * A ^ 2 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (2 / 3 : F) * D0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (2 / 9 : F) * A * B * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (5 / 6 : F) * E0 * deltaResidual610 L A B C0 D0 P Q S0 +
    (35 / 1296 : F) * A ^ 3 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * A * C0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 72 : F) * B ^ 2 * deltaResidual610 L A B C0 D0 P Q S0 +
    (20 / 243 : F) * A ^ 3 * B * alphaResidual610 A P -
    (4 / 27 : F) * A ^ 2 * D0 * alphaResidual610 A P -
    (8 / 27 : F) * A * B * C0 * alphaResidual610 A P -
    (4 / 81 : F) * B ^ 3 * alphaResidual610 A P +
    (4 / 9 : F) * B * E0 * alphaResidual610 A P +
    (4 / 9 : F) * C0 * D0 * alphaResidual610 A P +
    (385 / 31104 : F) * A ^ 4 * betaResidual610 L A B Q -
    (35 / 432 : F) * A ^ 2 * C0 * betaResidual610 L A B Q -
    (35 / 432 : F) * A * B ^ 2 * betaResidual610 L A B Q +
    (7 / 36 : F) * A * E0 * betaResidual610 L A B Q +
    (7 / 36 : F) * B * D0 * betaResidual610 L A B Q +
    (7 / 72 : F) * C0 ^ 2 * betaResidual610 L A B Q -
    (3 / 256 : F) * L * A ^ 5 +
    (3 / 32 : F) * L * A ^ 3 * C0 +
    (9 / 64 : F) * L * A ^ 2 * B ^ 2 -
    (3 / 16 : F) * L * A ^ 2 * E0 -
    (3 / 8 : F) * L * A * B * D0 -
    (3 / 16 : F) * L * A * C0 ^ 2 -
    (3 / 16 : F) * L * B ^ 2 * C0 +
    (3 / 4 : F) * L * C0 * E0 +
    (3 / 8 : F) * L * D0 ^ 2 -
    (35 / 729 : F) * A ^ 4 * B +
    (20 / 243 : F) * A ^ 3 * D0 +
    (20 / 81 : F) * A ^ 2 * B * C0 +
    (20 / 243 : F) * A * B ^ 3 -
    (10 / 27 : F) * A * B * E0 -
    (10 / 27 : F) * A * C0 * D0 -
    (5 / 27 : F) * B ^ 2 * D0 -
    (5 / 27 : F) * B * C0 ^ 2 +
    (10 / 9 : F) * D0 * E0

end BridgeKappaDepression610

end Max11DegreeRoutes
