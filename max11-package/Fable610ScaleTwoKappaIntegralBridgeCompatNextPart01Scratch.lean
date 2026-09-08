import Fable610ScaleTwoKappaIntegralBridgeCompatScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeLambdaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- First residual of the degree-`3` row, with `X'` eliminated through
the degree-`5` row.  Equivalent to
`(1/6) B θ - (1/9) A² η + (1/3) C η - (1/4) A B ζ + (1/2) D ζ
+ (4/81) A³ ε - (2/9) A C ε - (1/9) B² ε + (2/3) E ε + (35/432) A² B δ
- (5/36) A D δ - (5/36) B C δ - (8/729) A⁵ α + (20/243) A³ C α
+ (10/81) A² B² α - (4/27) A² E α - (8/27) A B D α - (4/27) A C² α
- (4/27) B² C α + (4/9) C E α + (2/9) D² α + (385/7776) A³ B β
- (35/432) A² D β - (35/216) A B C β - (35/1296) B³ β + (7/36) B E β
+ (7/36) C D β - (15/256) L A⁴ B + (3/32) L A³ D + (9/32) L A² B C
+ (3/32) L A B³ - (3/8) L A B E - (3/8) L A C D - (3/16) L B² D
- (3/16) L B C² + (3/4) L D E + (35/6561) A⁶ - (35/729) A⁴ C
- (70/729) A³ B² + (20/243) A³ E + (20/81) A² B D + (10/81) A² C²
+ (20/81) A B² C - (10/27) A C E - (5/27) A D² + (5/243) B⁴
- (5/27) B² E - (10/27) B C D - (5/81) C³ + (5/9) E²`
on the second- through ninth-face integrals. -/
def bridgeLambdaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 6 : F) * B * bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 -
    (1 / 9 : F) * A ^ 2 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 +
    (1 / 3 : F) * C0 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 -
    (1 / 4 : F) * A * B * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (1 / 2 : F) * D0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (4 / 81 : F) * A ^ 3 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (2 / 9 : F) * A * C0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (1 / 9 : F) * B ^ 2 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (2 / 3 : F) * E0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (35 / 432 : F) * A ^ 2 * B * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * A * D0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * B * C0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (8 / 729 : F) * A ^ 5 * alphaResidual610 A P +
    (20 / 243 : F) * A ^ 3 * C0 * alphaResidual610 A P +
    (10 / 81 : F) * A ^ 2 * B ^ 2 * alphaResidual610 A P -
    (4 / 27 : F) * A ^ 2 * E0 * alphaResidual610 A P -
    (8 / 27 : F) * A * B * D0 * alphaResidual610 A P -
    (4 / 27 : F) * A * C0 ^ 2 * alphaResidual610 A P -
    (4 / 27 : F) * B ^ 2 * C0 * alphaResidual610 A P +
    (4 / 9 : F) * C0 * E0 * alphaResidual610 A P +
    (2 / 9 : F) * D0 ^ 2 * alphaResidual610 A P +
    (385 / 7776 : F) * A ^ 3 * B * betaResidual610 L A B Q -
    (35 / 432 : F) * A ^ 2 * D0 * betaResidual610 L A B Q -
    (35 / 216 : F) * A * B * C0 * betaResidual610 L A B Q -
    (35 / 1296 : F) * B ^ 3 * betaResidual610 L A B Q +
    (7 / 36 : F) * B * E0 * betaResidual610 L A B Q +
    (7 / 36 : F) * C0 * D0 * betaResidual610 L A B Q -
    (15 / 256 : F) * L * A ^ 4 * B +
    (3 / 32 : F) * L * A ^ 3 * D0 +
    (9 / 32 : F) * L * A ^ 2 * B * C0 +
    (3 / 32 : F) * L * A * B ^ 3 -
    (3 / 8 : F) * L * A * B * E0 -
    (3 / 8 : F) * L * A * C0 * D0 -
    (3 / 16 : F) * L * B ^ 2 * D0 -
    (3 / 16 : F) * L * B * C0 ^ 2 +
    (3 / 4 : F) * L * D0 * E0 +
    (35 / 6561 : F) * A ^ 6 -
    (35 / 729 : F) * A ^ 4 * C0 -
    (70 / 729 : F) * A ^ 3 * B ^ 2 +
    (20 / 243 : F) * A ^ 3 * E0 +
    (20 / 81 : F) * A ^ 2 * B * D0 +
    (10 / 81 : F) * A ^ 2 * C0 ^ 2 +
    (20 / 81 : F) * A * B ^ 2 * C0 -
    (10 / 27 : F) * A * C0 * E0 -
    (5 / 27 : F) * A * D0 ^ 2 +
    (5 / 243 : F) * B ^ 4 -
    (5 / 27 : F) * B ^ 2 * E0 -
    (10 / 27 : F) * B * C0 * D0 -
    (5 / 81 : F) * C0 ^ 3 +
    (5 / 9 : F) * E0 ^ 2

end BridgeLambdaDepression610

end Max11DegreeRoutes
