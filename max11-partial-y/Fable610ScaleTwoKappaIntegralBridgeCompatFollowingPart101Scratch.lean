import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatNextScratch
import LowScale46SourceBridge

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
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepression610

variable {F : Type*} [Field F] [CharZero F]

-- Fix the carrier while retaining the original arithmetic heads and expression.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `12582912 h⁶⁵ μ` on the ninth-power face. -/
def bridgeClearedMuDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    - (180880 : F[X]) * a5 ^ 13
    + (88179 : F[X]) * a5 ^ 12 * Polynomial.C lambda * h ^ 5
    + (2015520 : F[X]) * a5 ^ 11 * a4 * h ^ 6
    + (268736 : F[X]) * a5 ^ 11 * b8 * h ^ 2
    - (1108536 : F[X]) * a5 ^ 10 * a4 * Polynomial.C lambda * h ^ 11
    - (2139280 : F[X]) * a5 ^ 10 * a3 * h ^ 12
    - (272272 : F[X]) * a5 ^ 10 * b7 * h ^ 8
    - (7779200 : F[X]) * a5 ^ 9 * a4 ^ 2 * h ^ 12
    - (3111680 : F[X]) * a5 ^ 9 * a4 * b8 * h ^ 8
    + (1166880 : F[X]) * a5 ^ 9 * a3 * Polynomial.C lambda * h ^ 17
    + (2288000 : F[X]) * a5 ^ 9 * a2 * h ^ 18
    + (274560 : F[X]) * a5 ^ 9 * b6 * h ^ 14
    + (5250960 : F[X]) * a5 ^ 8 * a4 ^ 2 * Polynomial.C lambda * h ^ 17
    + (14414400 : F[X]) * a5 ^ 8 * a4 * a3 * h ^ 18
    + (2882880 : F[X]) * a5 ^ 8 * a4 * b7 * h ^ 14
    + (3294720 : F[X]) * a5 ^ 8 * a3 * b8 * h ^ 14
    - (1235520 : F[X]) * a5 ^ 8 * a2 * Polynomial.C lambda * h ^ 23
    - (2471040 : F[X]) * a5 ^ 8 * a1 * h ^ 24
    - (274560 : F[X]) * a5 ^ 8 * b5 * h ^ 20
    + (10982400 : F[X]) * a5 ^ 7 * a4 ^ 3 * h ^ 18
    + (13178880 : F[X]) * a5 ^ 7 * a4 ^ 2 * b8 * h ^ 14
    - (9884160 : F[X]) * a5 ^ 7 * a4 * a3 * Polynomial.C lambda * h ^ 23
    - (13178880 : F[X]) * a5 ^ 7 * a4 * a2 * h ^ 24
    - (2635776 : F[X]) * a5 ^ 7 * a4 * b6 * h ^ 20
    - (6589440 : F[X]) * a5 ^ 7 * a3 ^ 2 * h ^ 24
    - (3075072 : F[X]) * a5 ^ 7 * a3 * b7 * h ^ 20
    - (3514368 : F[X]) * a5 ^ 7 * a2 * b8 * h ^ 20
    + (1317888 : F[X]) * a5 ^ 7 * a1 * Polynomial.C lambda * h ^ 29
    + (2703360 : F[X]) * a5 ^ 7 * a0 * h ^ 30
    + (270336 : F[X]) * a5 ^ 7 * b4 * h ^ 26
    - (11531520 : F[X]) * a5 ^ 6 * a4 ^ 3 * Polynomial.C lambda * h ^ 23
    - (23063040 : F[X]) * a5 ^ 6 * a4 ^ 2 * a3 * h ^ 24
    - (10762752 : F[X]) * a5 ^ 6 * a4 ^ 2 * b7 * h ^ 20
    - (24600576 : F[X]) * a5 ^ 6 * a4 * a3 * b8 * h ^ 20
    + (9225216 : F[X]) * a5 ^ 6 * a4 * a2 * Polynomial.C lambda * h ^ 29
    + (11827200 : F[X]) * a5 ^ 6 * a4 * a1 * h ^ 30
    + (2365440 : F[X]) * a5 ^ 6 * a4 * b5 * h ^ 26
    + (4612608 : F[X]) * a5 ^ 6 * a3 ^ 2 * Polynomial.C lambda * h ^ 29
    + (11827200 : F[X]) * a5 ^ 6 * a3 * a2 * h ^ 30
    + (2838528 : F[X]) * a5 ^ 6 * a3 * b6 * h ^ 26
    + (3311616 : F[X]) * a5 ^ 6 * a2 * b7 * h ^ 26
    + (3784704 : F[X]) * a5 ^ 6 * a1 * b8 * h ^ 26
    - (1419264 : F[X]) * a5 ^ 6 * a0 * Polynomial.C lambda * h ^ 35
    - (258048 : F[X]) * a5 ^ 6 * b3 * h ^ 32
    - (24600576 : F[X]) * a5 ^ 5 * a4 ^ 3 * b8 * h ^ 20
    + (27675648 : F[X]) * a5 ^ 5 * a4 ^ 2 * a3 * Polynomial.C lambda * h ^ 29
    + (14192640 : F[X]) * a5 ^ 5 * a4 ^ 2 * a2 * h ^ 30
    + (8515584 : F[X]) * a5 ^ 5 * a4 ^ 2 * b6 * h ^ 26
    + (14192640 : F[X]) * a5 ^ 5 * a4 * a3 ^ 2 * h ^ 30
    + (19869696 : F[X]) * a5 ^ 5 * a4 * a3 * b7 * h ^ 26
    + (22708224 : F[X]) * a5 ^ 5 * a4 * a2 * b8 * h ^ 26
    - (8515584 : F[X]) * a5 ^ 5 * a4 * a1 * Polynomial.C lambda * h ^ 35
    - (10321920 : F[X]) * a5 ^ 5 * a4 * a0 * h ^ 36
    - (2064384 : F[X]) * a5 ^ 5 * a4 * b4 * h ^ 32
    + (11354112 : F[X]) * a5 ^ 5 * a3 ^ 2 * b8 * h ^ 26
    - (8515584 : F[X]) * a5 ^ 5 * a3 * a2 * Polynomial.C lambda * h ^ 35
    - (10321920 : F[X]) * a5 ^ 5 * a3 * a1 * h ^ 36
    - (2580480 : F[X]) * a5 ^ 5 * a3 * b5 * h ^ 32
    - (5160960 : F[X]) * a5 ^ 5 * a2 ^ 2 * h ^ 36
    - (3096576 : F[X]) * a5 ^ 5 * a2 * b6 * h ^ 32
    - (3612672 : F[X]) * a5 ^ 5 * a1 * b7 * h ^ 32
    - (4128768 : F[X]) * a5 ^ 5 * a0 * b8 * h ^ 32
    + (229376 : F[X]) * a5 ^ 5 * b2 * h ^ 38
    + (11531520 : F[X]) * a5 ^ 4 * a4 ^ 4 * Polynomial.C lambda * h ^ 29
    - (11827200 : F[X]) * a5 ^ 4 * a4 ^ 3 * a3 * h ^ 30
    + (16558080 : F[X]) * a5 ^ 4 * a4 ^ 3 * b7 * h ^ 26
    + (56770560 : F[X]) * a5 ^ 4 * a4 ^ 2 * a3 * b8 * h ^ 26
    - (21288960 : F[X]) * a5 ^ 4 * a4 ^ 2 * a2 * Polynomial.C lambda * h ^ 35
    - (6451200 : F[X]) * a5 ^ 4 * a4 ^ 2 * a1 * h ^ 36
    - (6451200 : F[X]) * a5 ^ 4 * a4 ^ 2 * b5 * h ^ 32
    - (21288960 : F[X]) * a5 ^ 4 * a4 * a3 ^ 2 * Polynomial.C lambda * h ^ 35
    - (12902400 : F[X]) * a5 ^ 4 * a4 * a3 * a2 * h ^ 36
    - (15482880 : F[X]) * a5 ^ 4 * a4 * a3 * b6 * h ^ 32
    - (18063360 : F[X]) * a5 ^ 4 * a4 * a2 * b7 * h ^ 32
    - (20643840 : F[X]) * a5 ^ 4 * a4 * a1 * b8 * h ^ 32
    + (7741440 : F[X]) * a5 ^ 4 * a4 * a0 * Polynomial.C lambda * h ^ 41
    + (1720320 : F[X]) * a5 ^ 4 * a4 * b3 * h ^ 38
    - (2150400 : F[X]) * a5 ^ 4 * a3 ^ 3 * h ^ 36
    - (9031680 : F[X]) * a5 ^ 4 * a3 ^ 2 * b7 * h ^ 32
    - (20643840 : F[X]) * a5 ^ 4 * a3 * a2 * b8 * h ^ 32
    + (7741440 : F[X]) * a5 ^ 4 * a3 * a1 * Polynomial.C lambda * h ^ 41
    + (8601600 : F[X]) * a5 ^ 4 * a3 * a0 * h ^ 42
    + (2293760 : F[X]) * a5 ^ 4 * a3 * b4 * h ^ 38
    + (3870720 : F[X]) * a5 ^ 4 * a2 ^ 2 * Polynomial.C lambda * h ^ 41
    + (8601600 : F[X]) * a5 ^ 4 * a2 * a1 * h ^ 42
    + (2867200 : F[X]) * a5 ^ 4 * a2 * b5 * h ^ 38
    + (3440640 : F[X]) * a5 ^ 4 * a1 * b6 * h ^ 38
    + (4014080 : F[X]) * a5 ^ 4 * a0 * b7 * h ^ 38
    - (163840 : F[X]) * a5 ^ 4 * b1 * h ^ 44
    - (9461760 : F[X]) * a5 ^ 3 * a4 ^ 5 * h ^ 30
    + (18923520 : F[X]) * a5 ^ 3 * a4 ^ 4 * b8 * h ^ 26
    - (28385280 : F[X]) * a5 ^ 3 * a4 ^ 3 * a3 * Polynomial.C lambda * h ^ 35
    + (17203200 : F[X]) * a5 ^ 3 * a4 ^ 3 * a2 * h ^ 36
    - (10321920 : F[X]) * a5 ^ 3 * a4 ^ 3 * b6 * h ^ 32
    + (25804800 : F[X]) * a5 ^ 3 * a4 ^ 2 * a3 ^ 2 * h ^ 36
    - (36126720 : F[X]) * a5 ^ 3 * a4 ^ 2 * a3 * b7 * h ^ 32
    - (41287680 : F[X]) * a5 ^ 3 * a4 ^ 2 * a2 * b8 * h ^ 32
    + (15482880 : F[X]) * a5 ^ 3 * a4 ^ 2 * a1 * Polynomial.C lambda * h ^ 41
    + (4587520 : F[X]) * a5 ^ 3 * a4 ^ 2 * b4 * h ^ 38
    - (41287680 : F[X]) * a5 ^ 3 * a4 * a3 ^ 2 * b8 * h ^ 32
    + (30965760 : F[X]) * a5 ^ 3 * a4 * a3 * a2 * Polynomial.C lambda * h ^ 41
    + (11468800 : F[X]) * a5 ^ 3 * a4 * a3 * b5 * h ^ 38
    + (13762560 : F[X]) * a5 ^ 3 * a4 * a2 * b6 * h ^ 38
    + (16056320 : F[X]) * a5 ^ 3 * a4 * a1 * b7 * h ^ 38
    + (18350080 : F[X]) * a5 ^ 3 * a4 * a0 * b8 * h ^ 38
    - (1310720 : F[X]) * a5 ^ 3 * a4 * b2 * h ^ 44
    + (5160960 : F[X]) * a5 ^ 3 * a3 ^ 3 * Polynomial.C lambda * h ^ 41
    + (6881280 : F[X]) * a5 ^ 3 * a3 ^ 2 * b6 * h ^ 38
    + (16056320 : F[X]) * a5 ^ 3 * a3 * a2 * b7 * h ^ 38
    + (18350080 : F[X]) * a5 ^ 3 * a3 * a1 * b8 * h ^ 38
    - (6881280 : F[X]) * a5 ^ 3 * a3 * a0 * Polynomial.C lambda * h ^ 47
    - (1966080 : F[X]) * a5 ^ 3 * a3 * b3 * h ^ 44
    + (9175040 : F[X]) * a5 ^ 3 * a2 ^ 2 * b8 * h ^ 38
    - (6881280 : F[X]) * a5 ^ 3 * a2 * a1 * Polynomial.C lambda * h ^ 47
    - (6553600 : F[X]) * a5 ^ 3 * a2 * a0 * h ^ 48
    - (2621440 : F[X]) * a5 ^ 3 * a2 * b4 * h ^ 44
    - (3276800 : F[X]) * a5 ^ 3 * a1 ^ 2 * h ^ 48
    - (3276800 : F[X]) * a5 ^ 3 * a1 * b5 * h ^ 44
    - (3932160 : F[X]) * a5 ^ 3 * a0 * b6 * h ^ 44
    - (4257792 : F[X]) * a5 ^ 2 * a4 ^ 5 * Polynomial.C lambda * h ^ 35
    + (32256000 : F[X]) * a5 ^ 2 * a4 ^ 4 * a3 * h ^ 36
    - (9031680 : F[X]) * a5 ^ 2 * a4 ^ 4 * b7 * h ^ 32
    - (41287680 : F[X]) * a5 ^ 2 * a4 ^ 3 * a3 * b8 * h ^ 32
    + (15482880 : F[X]) * a5 ^ 2 * a4 ^ 3 * a2 * Polynomial.C lambda * h ^ 41
    - (17203200 : F[X]) * a5 ^ 2 * a4 ^ 3 * a1 * h ^ 42
    + (5734400 : F[X]) * a5 ^ 2 * a4 ^ 3 * b5 * h ^ 38
    + (23224320 : F[X]) * a5 ^ 2 * a4 ^ 2 * a3 ^ 2 * Polynomial.C lambda * h ^ 41
    - (51609600 : F[X]) * a5 ^ 2 * a4 ^ 2 * a3 * a2 * h ^ 42
    + (20643840 : F[X]) * a5 ^ 2 * a4 ^ 2 * a3 * b6 * h ^ 38
    + (24084480 : F[X]) * a5 ^ 2 * a4 ^ 2 * a2 * b7 * h ^ 38
    + (27525120 : F[X]) * a5 ^ 2 * a4 ^ 2 * a1 * b8 * h ^ 38
    - (10321920 : F[X]) * a5 ^ 2 * a4 ^ 2 * a0 * Polynomial.C lambda * h ^ 47
    - (2949120 : F[X]) * a5 ^ 2 * a4 ^ 2 * b3 * h ^ 44
    - (17203200 : F[X]) * a5 ^ 2 * a4 * a3 ^ 3 * h ^ 42
    + (24084480 : F[X]) * a5 ^ 2 * a4 * a3 ^ 2 * b7 * h ^ 38
    + (55050240 : F[X]) * a5 ^ 2 * a4 * a3 * a2 * b8 * h ^ 38
    - (20643840 : F[X]) * a5 ^ 2 * a4 * a3 * a1 * Polynomial.C lambda * h ^ 47
    + (9830400 : F[X]) * a5 ^ 2 * a4 * a3 * a0 * h ^ 48
    - (7864320 : F[X]) * a5 ^ 2 * a4 * a3 * b4 * h ^ 44
    - (10321920 : F[X]) * a5 ^ 2 * a4 * a2 ^ 2 * Polynomial.C lambda * h ^ 47
    + (9830400 : F[X]) * a5 ^ 2 * a4 * a2 * a1 * h ^ 48
    - (9830400 : F[X]) * a5 ^ 2 * a4 * a2 * b5 * h ^ 44
    - (11796480 : F[X]) * a5 ^ 2 * a4 * a1 * b6 * h ^ 44
    - (13762560 : F[X]) * a5 ^ 2 * a4 * a0 * b7 * h ^ 44
    + (786432 : F[X]) * a5 ^ 2 * a4 * b1 * h ^ 50
    + (9175040 : F[X]) * a5 ^ 2 * a3 ^ 3 * b8 * h ^ 38
    - (10321920 : F[X]) * a5 ^ 2 * a3 ^ 2 * a2 * Polynomial.C lambda * h ^ 47
    + (4915200 : F[X]) * a5 ^ 2 * a3 ^ 2 * a1 * h ^ 48
    - (4915200 : F[X]) * a5 ^ 2 * a3 ^ 2 * b5 * h ^ 44
    + (4915200 : F[X]) * a5 ^ 2 * a3 * a2 ^ 2 * h ^ 48
    - (11796480 : F[X]) * a5 ^ 2 * a3 * a2 * b6 * h ^ 44
    - (13762560 : F[X]) * a5 ^ 2 * a3 * a1 * b7 * h ^ 44
    - (15728640 : F[X]) * a5 ^ 2 * a3 * a0 * b8 * h ^ 44
    + (1572864 : F[X]) * a5 ^ 2 * a3 * b2 * h ^ 50
    - (6881280 : F[X]) * a5 ^ 2 * a2 ^ 2 * b7 * h ^ 44
    - (15728640 : F[X]) * a5 ^ 2 * a2 * a1 * b8 * h ^ 44
    + (5898240 : F[X]) * a5 ^ 2 * a2 * a0 * Polynomial.C lambda * h ^ 53
    + (2359296 : F[X]) * a5 ^ 2 * a2 * b3 * h ^ 50
    + (2949120 : F[X]) * a5 ^ 2 * a1 ^ 2 * Polynomial.C lambda * h ^ 53
    + (3932160 : F[X]) * a5 ^ 2 * a1 * a0 * h ^ 54
    + (3145728 : F[X]) * a5 ^ 2 * a1 * b4 * h ^ 50
    + (3932160 : F[X]) * a5 ^ 2 * a0 * b5 * h ^ 50
    + (3440640 : F[X]) * a5 * a4 ^ 6 * h ^ 36
    - (4128768 : F[X]) * a5 * a4 ^ 5 * b8 * h ^ 32
    + (7741440 : F[X]) * a5 * a4 ^ 4 * a3 * Polynomial.C lambda * h ^ 41
    - (17203200 : F[X]) * a5 * a4 ^ 4 * a2 * h ^ 42
    + (3440640 : F[X]) * a5 * a4 ^ 4 * b6 * h ^ 38
    - (34406400 : F[X]) * a5 * a4 ^ 3 * a3 ^ 2 * h ^ 42
    + (16056320 : F[X]) * a5 * a4 ^ 3 * a3 * b7 * h ^ 38
    + (18350080 : F[X]) * a5 * a4 ^ 3 * a2 * b8 * h ^ 38
    - (6881280 : F[X]) * a5 * a4 ^ 3 * a1 * Polynomial.C lambda * h ^ 47
    + (13107200 : F[X]) * a5 * a4 ^ 3 * a0 * h ^ 48
    - (2621440 : F[X]) * a5 * a4 ^ 3 * b4 * h ^ 44
    + (27525120 : F[X]) * a5 * a4 ^ 2 * a3 ^ 2 * b8 * h ^ 38
    - (20643840 : F[X]) * a5 * a4 ^ 2 * a3 * a2 * Polynomial.C lambda * h ^ 47
    + (39321600 : F[X]) * a5 * a4 ^ 2 * a3 * a1 * h ^ 48
    - (9830400 : F[X]) * a5 * a4 ^ 2 * a3 * b5 * h ^ 44
    + (19660800 : F[X]) * a5 * a4 ^ 2 * a2 ^ 2 * h ^ 48
    - (11796480 : F[X]) * a5 * a4 ^ 2 * a2 * b6 * h ^ 44
    - (13762560 : F[X]) * a5 * a4 ^ 2 * a1 * b7 * h ^ 44
    - (15728640 : F[X]) * a5 * a4 ^ 2 * a0 * b8 * h ^ 44
    + (1572864 : F[X]) * a5 * a4 ^ 2 * b2 * h ^ 50
    - (6881280 : F[X]) * a5 * a4 * a3 ^ 3 * Polynomial.C lambda * h ^ 47
    + (39321600 : F[X]) * a5 * a4 * a3 ^ 2 * a2 * h ^ 48
    - (11796480 : F[X]) * a5 * a4 * a3 ^ 2 * b6 * h ^ 44
    - (27525120 : F[X]) * a5 * a4 * a3 * a2 * b7 * h ^ 44
    - (31457280 : F[X]) * a5 * a4 * a3 * a1 * b8 * h ^ 44
    + (11796480 : F[X]) * a5 * a4 * a3 * a0 * Polynomial.C lambda * h ^ 53
    + (4718592 : F[X]) * a5 * a4 * a3 * b3 * h ^ 50
    - (15728640 : F[X]) * a5 * a4 * a2 ^ 2 * b8 * h ^ 44
    + (11796480 : F[X]) * a5 * a4 * a2 * a1 * Polynomial.C lambda * h ^ 53
    - (15728640 : F[X]) * a5 * a4 * a2 * a0 * h ^ 54
    + (6291456 : F[X]) * a5 * a4 * a2 * b4 * h ^ 50
    - (7864320 : F[X]) * a5 * a4 * a1 ^ 2 * h ^ 54
    + (7864320 : F[X]) * a5 * a4 * a1 * b5 * h ^ 50
    + (9437184 : F[X]) * a5 * a4 * a0 * b6 * h ^ 50
    + (3276800 : F[X]) * a5 * a3 ^ 4 * h ^ 48
    - (4587520 : F[X]) * a5 * a3 ^ 3 * b7 * h ^ 44
    - (15728640 : F[X]) * a5 * a3 ^ 2 * a2 * b8 * h ^ 44
    + (5898240 : F[X]) * a5 * a3 ^ 2 * a1 * Polynomial.C lambda * h ^ 53
    - (7864320 : F[X]) * a5 * a3 ^ 2 * a0 * h ^ 54
    + (3145728 : F[X]) * a5 * a3 ^ 2 * b4 * h ^ 50
    + (5898240 : F[X]) * a5 * a3 * a2 ^ 2 * Polynomial.C lambda * h ^ 53
    - (15728640 : F[X]) * a5 * a3 * a2 * a1 * h ^ 54
    + (7864320 : F[X]) * a5 * a3 * a2 * b5 * h ^ 50
    + (9437184 : F[X]) * a5 * a3 * a1 * b6 * h ^ 50
    + (11010048 : F[X]) * a5 * a3 * a0 * b7 * h ^ 50
    - (1048576 : F[X]) * a5 * a3 * b1 * h ^ 56
    - (2621440 : F[X]) * a5 * a2 ^ 3 * h ^ 54
    + (4718592 : F[X]) * a5 * a2 ^ 2 * b6 * h ^ 50
    + (11010048 : F[X]) * a5 * a2 * a1 * b7 * h ^ 50
    + (12582912 : F[X]) * a5 * a2 * a0 * b8 * h ^ 50
    - (2097152 : F[X]) * a5 * a2 * b2 * h ^ 56
    + (6291456 : F[X]) * a5 * a1 ^ 2 * b8 * h ^ 50
    - (4718592 : F[X]) * a5 * a1 * a0 * Polynomial.C lambda * h ^ 59
    - (3145728 : F[X]) * a5 * a1 * b3 * h ^ 56
    - (4194304 : F[X]) * a5 * a0 * b4 * h ^ 56
    + (258048 : F[X]) * a4 ^ 6 * Polynomial.C lambda * h ^ 41
    - (5160960 : F[X]) * a4 ^ 5 * a3 * h ^ 42
    + (802816 : F[X]) * a4 ^ 5 * b7 * h ^ 38
    + (4587520 : F[X]) * a4 ^ 4 * a3 * b8 * h ^ 38
    - (1720320 : F[X]) * a4 ^ 4 * a2 * Polynomial.C lambda * h ^ 47
    + (5734400 : F[X]) * a4 ^ 4 * a1 * h ^ 48
    - (819200 : F[X]) * a4 ^ 4 * b5 * h ^ 44
    - (3440640 : F[X]) * a4 ^ 3 * a3 ^ 2 * Polynomial.C lambda * h ^ 47
    + (22937600 : F[X]) * a4 ^ 3 * a3 * a2 * h ^ 48
    - (3932160 : F[X]) * a4 ^ 3 * a3 * b6 * h ^ 44
    - (4587520 : F[X]) * a4 ^ 3 * a2 * b7 * h ^ 44
    - (5242880 : F[X]) * a4 ^ 3 * a1 * b8 * h ^ 44
    + (1966080 : F[X]) * a4 ^ 3 * a0 * Polynomial.C lambda * h ^ 53
    + (786432 : F[X]) * a4 ^ 3 * b3 * h ^ 50
    + (11468800 : F[X]) * a4 ^ 2 * a3 ^ 3 * h ^ 48
    - (6881280 : F[X]) * a4 ^ 2 * a3 ^ 2 * b7 * h ^ 44
    - (15728640 : F[X]) * a4 ^ 2 * a3 * a2 * b8 * h ^ 44
    + (5898240 : F[X]) * a4 ^ 2 * a3 * a1 * Polynomial.C lambda * h ^ 53
    - (19660800 : F[X]) * a4 ^ 2 * a3 * a0 * h ^ 54
    + (3145728 : F[X]) * a4 ^ 2 * a3 * b4 * h ^ 50
    + (2949120 : F[X]) * a4 ^ 2 * a2 ^ 2 * Polynomial.C lambda * h ^ 53
    - (19660800 : F[X]) * a4 ^ 2 * a2 * a1 * h ^ 54
    + (3932160 : F[X]) * a4 ^ 2 * a2 * b5 * h ^ 50
    + (4718592 : F[X]) * a4 ^ 2 * a1 * b6 * h ^ 50
    + (5505024 : F[X]) * a4 ^ 2 * a0 * b7 * h ^ 50
    - (524288 : F[X]) * a4 ^ 2 * b1 * h ^ 56
    - (5242880 : F[X]) * a4 * a3 ^ 3 * b8 * h ^ 44
    + (5898240 : F[X]) * a4 * a3 ^ 2 * a2 * Polynomial.C lambda * h ^ 53
    - (19660800 : F[X]) * a4 * a3 ^ 2 * a1 * h ^ 54
    + (3932160 : F[X]) * a4 * a3 ^ 2 * b5 * h ^ 50
    - (19660800 : F[X]) * a4 * a3 * a2 ^ 2 * h ^ 54
    + (9437184 : F[X]) * a4 * a3 * a2 * b6 * h ^ 50
    + (11010048 : F[X]) * a4 * a3 * a1 * b7 * h ^ 50
    + (12582912 : F[X]) * a4 * a3 * a0 * b8 * h ^ 50
    - (2097152 : F[X]) * a4 * a3 * b2 * h ^ 56
    + (5505024 : F[X]) * a4 * a2 ^ 2 * b7 * h ^ 50
    + (12582912 : F[X]) * a4 * a2 * a1 * b8 * h ^ 50
    - (4718592 : F[X]) * a4 * a2 * a0 * Polynomial.C lambda * h ^ 59
    - (3145728 : F[X]) * a4 * a2 * b3 * h ^ 56
    - (2359296 : F[X]) * a4 * a1 ^ 2 * Polynomial.C lambda * h ^ 59
    + (15728640 : F[X]) * a4 * a1 * a0 * h ^ 60
    - (4194304 : F[X]) * a4 * a1 * b4 * h ^ 56
    - (5242880 : F[X]) * a4 * a0 * b5 * h ^ 56
    + (491520 : F[X]) * a3 ^ 4 * Polynomial.C lambda * h ^ 53
    - (6553600 : F[X]) * a3 ^ 3 * a2 * h ^ 54
    + (1572864 : F[X]) * a3 ^ 3 * b6 * h ^ 50
    + (5505024 : F[X]) * a3 ^ 2 * a2 * b7 * h ^ 50
    + (6291456 : F[X]) * a3 ^ 2 * a1 * b8 * h ^ 50
    - (2359296 : F[X]) * a3 ^ 2 * a0 * Polynomial.C lambda * h ^ 59
    - (1572864 : F[X]) * a3 ^ 2 * b3 * h ^ 56
    + (6291456 : F[X]) * a3 * a2 ^ 2 * b8 * h ^ 50
    - (4718592 : F[X]) * a3 * a2 * a1 * Polynomial.C lambda * h ^ 59
    + (15728640 : F[X]) * a3 * a2 * a0 * h ^ 60
    - (4194304 : F[X]) * a3 * a2 * b4 * h ^ 56
    + (7864320 : F[X]) * a3 * a1 ^ 2 * h ^ 60
    - (5242880 : F[X]) * a3 * a1 * b5 * h ^ 56
    - (6291456 : F[X]) * a3 * a0 * b6 * h ^ 56
    - (786432 : F[X]) * a2 ^ 3 * Polynomial.C lambda * h ^ 59
    + (7864320 : F[X]) * a2 ^ 2 * a1 * h ^ 60
    - (2621440 : F[X]) * a2 ^ 2 * b5 * h ^ 56
    - (6291456 : F[X]) * a2 * a1 * b6 * h ^ 56
    - (7340032 : F[X]) * a2 * a0 * b7 * h ^ 56
    + (2097152 : F[X]) * a2 * b1 * h ^ 62
    - (3670016 : F[X]) * a1 ^ 2 * b7 * h ^ 56
    - (8388608 : F[X]) * a1 * a0 * b8 * h ^ 56
    + (4194304 : F[X]) * a1 * b2 * h ^ 62
    + (1572864 : F[X]) * a0 ^ 2 * Polynomial.C lambda * h ^ 65
    + (6291456 : F[X]) * a0 * b3 * h ^ 62

end BridgeMuDepression610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic, the degree-`2`
Jacobian coefficient is exactly `3 U E' + 2 V D' + W C'
- D V' - 2 C W' - 3 B X'`. -/
theorem differentialJacobian_coeff_2_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 6 < n → f.coeff n = 0) (_hf6 : f.coeff 6 = 1)
    (_hf5 : f.coeff 5 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        (1 : F) * g.coeff 1 * d (f.coeff 2) -
          (1 : F) * f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) -
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne02_11 : ((0, 2) : ℕ × ℕ) ≠ (1, 1) := by decide
  have hne02_20 : ((0, 2) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hne11_20 : ((1, 1) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 2 =
        (3 : F) * g.coeff 3 * d (f.coeff 0) +
          (2 : F) * g.coeff 2 * d (f.coeff 1) +
          (1 : F) * g.coeff 1 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]), Finset.sum_singleton]
      ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder2g, hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 2 =
        (1 : F) * f.coeff 1 * d (g.coeff 2) +
          (2 : F) * f.coeff 2 * d (g.coeff 1) +
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end BridgeMuDepressedRow610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJet610

variable {R : Type*} [CommRing R]

/-- Order-`59` head of the jet-substituted cleared `μ` defect: the
coefficient of `h⁵⁹` after the globally merged jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h² p₃₂`, `q₈ = h⁷ s₁`, `q₇ = h⁶ u₂`,
`q₆ = h⁴ b₆₂`, `q₅ = h³ q₅₃`, `q₄ = h q₄₁` is substituted into
`bridgeClearedMuDefect610`, kept factored through its content
`4096`. -/
def bridgeMuJetHead610
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 lam : R) : R :=
  (4096 : R) *
    ((840 : R) * a41 ^ 6 * w1
      + (63 : R) * a41 ^ 6 * lam
      - (1260 : R) * a41 ^ 5 * p32
      - (1008 : R) * a41 ^ 5 * s1 * w1
      + (196 : R) * a41 ^ 5 * u2
      - (4200 : R) * a41 ^ 4 * p2 * w1
      - (420 : R) * a41 ^ 4 * p2 * lam
      + (1120 : R) * a41 ^ 4 * p32 * s1
      + (840 : R) * a41 ^ 4 * b62 * w1
      - (200 : R) * a41 ^ 4 * q53
      + (5600 : R) * a41 ^ 3 * p2 * p32
      + (4480 : R) * a41 ^ 3 * p2 * s1 * w1
      - (1120 : R) * a41 ^ 3 * p2 * u2
      - (960 : R) * a41 ^ 3 * p32 * b62
      - (640 : R) * a41 ^ 3 * q41 * w1
      + (192 : R) * a41 ^ 3 * q3
      + (4800 : R) * a41 ^ 2 * p2 ^ 2 * w1
      + (720 : R) * a41 ^ 2 * p2 ^ 2 * lam
      - (3840 : R) * a41 ^ 2 * p2 * p32 * s1
      - (2880 : R) * a41 ^ 2 * p2 * b62 * w1
      + (960 : R) * a41 ^ 2 * p2 * q53
      + (768 : R) * a41 ^ 2 * p32 * q41
      - (4800 : R) * a41 * p2 ^ 2 * p32
      - (3840 : R) * a41 * p2 ^ 2 * s1 * w1
      + (1344 : R) * a41 * p2 ^ 2 * u2
      + (2304 : R) * a41 * p2 * p32 * b62
      + (1536 : R) * a41 * p2 * q41 * w1
      - (768 : R) * a41 * p2 * q3
      - (640 : R) * p2 ^ 3 * w1
      - (192 : R) * p2 ^ 3 * lam
      + (1536 : R) * p2 ^ 2 * p32 * s1
      + (1152 : R) * p2 ^ 2 * b62 * w1
      - (640 : R) * p2 ^ 2 * q53
      - (1024 : R) * p2 * p32 * q41)

end BridgeMuJet610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJet610

variable {R : Type*} [CommRing R]

/-- Order-`61` head of the sibling-child deep jet: the coefficient of
`h⁶¹` after the deeper jet `p₄ = h⁴ a₄₂`, `p₂ = h p₂₁`, `q₈ = h⁸ s₂`,
`q₆ = h⁵ b₆₃`, `q₅ = h⁴ q₅₄`, `q₄ = h² q₄₂`, `q₃ = h q₃₁` is
substituted into `bridgeClearedMuDefect610`, kept factored as
`32768 p₃₂` times its cofactor. -/
def bridgeMuDeepHead610
    (w1 p32 u2 b63 p21 q42 q31 lam : R) : R :=
  (32768 : R) * p32 *
    ((100 : R) * p32 ^ 3 * w1
      + (15 : R) * p32 ^ 3 * lam
      + (48 : R) * p32 ^ 2 * b63
      - (200 : R) * p32 ^ 2 * p21
      - (140 : R) * p32 ^ 2 * u2 * w1
      + (168 : R) * p32 * p21 * u2
      + (96 : R) * p32 * q42 * w1
      - (48 : R) * p32 * q31
      - (128 : R) * p21 * q42)

end BridgeMuJet610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the pinned complement child with the `q`-jet pin the
chamber-free relation factors as `a₄₁³ · G = 0` — the honest split
`a₄₁ = 0 ∨ 15552 q₃ = -2943 λ a₄₁³ + 14040 a₄₁³ w₁ + 1060 a₄₁² p₃₂
- 11340 a₄₁² u₂ + 14040 a₄₁ q₅₃`. -/
theorem bridgeMu_complementSplit610
    (w1 a41 p32 u2 q53 q41 q3 p2 lam : F)
    (hR : - (1120 : F) * a41 ^ 6 * w1
    + (189 : F) * a41 ^ 6 * lam
    + (220 : F) * a41 ^ 5 * p32
    + (588 : F) * a41 ^ 5 * u2
    + (9200 : F) * a41 ^ 4 * p2 * w1
    - (1260 : F) * a41 ^ 4 * p2 * lam
    - (600 : F) * a41 ^ 4 * q53
    - (3360 : F) * a41 ^ 3 * p2 * p32
    - (3360 : F) * a41 ^ 3 * p2 * u2
    - (1920 : F) * a41 ^ 3 * q41 * w1
    + (576 : F) * a41 ^ 3 * q3
    - (17280 : F) * a41 ^ 2 * p2 ^ 2 * w1
    + (2160 : F) * a41 ^ 2 * p2 ^ 2 * lam
    + (2880 : F) * a41 ^ 2 * p2 * q53
    + (2304 : F) * a41 ^ 2 * p32 * q41
    + (4800 : F) * a41 * p2 ^ 2 * p32
    + (4032 : F) * a41 * p2 ^ 2 * u2
    + (4608 : F) * a41 * p2 * q41 * w1
    - (2304 : F) * a41 * p2 * q3
    + (3840 : F) * p2 ^ 3 * w1
    - (576 : F) * p2 ^ 3 * lam
    - (1920 : F) * p2 ^ 2 * q53
    - (3072 : F) * p2 * p32 * q41 = 0)
    (hpin : (6 : F) * p2 - a41 ^ 2 = 0)
    (hq41 : (324 : F) * q41 = (35 : F) * a41 ^ 3) :
    a41 = 0 ∨
      (15552 : F) * q3 =
        -(2943 : F) * lam * a41 ^ 3 + (14040 : F) * a41 ^ 3 * w1 +
          (1060 : F) * a41 ^ 2 * p32 - (11340 : F) * a41 ^ 2 * u2 +
          (14040 : F) * a41 * q53 := by
  have hprod : a41 ^ 3 *
      ((14040 : F) * a41 ^ 3 * w1 - (2943 : F) * a41 ^ 3 * lam +
        (1060 : F) * a41 ^ 2 * p32 - (11340 : F) * a41 ^ 2 * u2 +
        (14040 : F) * a41 * q53 - (15552 : F) * q3) = 0 := by
    linear_combination (-81 : F) * hR +
      ((86760 : F) * a41 ^ 4 * w1 - (12366 : F) * a41 ^ 4 * lam -
        (34560 : F) * a41 ^ 3 * p32 - (36288 : F) * a41 ^ 3 * u2 -
        (224640 : F) * a41 ^ 2 * p2 * w1 +
        (27864 : F) * a41 ^ 2 * p2 * lam + (34560 : F) * a41 ^ 2 * q53 +
        (64800 : F) * a41 * p2 * p32 + (54432 : F) * a41 * p2 * u2 +
        (62208 : F) * a41 * q41 * w1 - (31104 : F) * a41 * q3 +
        (51840 : F) * p2 ^ 2 * w1 - (7776 : F) * p2 ^ 2 * lam -
        (25920 : F) * p2 * q53 - (41472 : F) * p32 * q41) * hpin +
      (-(288 : F) * a41 ^ 3 * w1 + (448 : F) * a41 ^ 2 * p32) * hq41
  rcases mul_eq_zero.mp hprod with h3 | hlin
  · left
    by_contra hne
    exact pow_ne_zero 3 hne h3
  · right
    linear_combination -hlin

end BridgeMuScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem bridgeMuResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (htheta : d (bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0)
    (hrow6 : (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - (1 : F) * D0 * d R -
        (2 : F) * C0 * d S0 - (3 : F) * B * d T0 -
        (4 : F) * A * d U0 - (6 : F) * d W0 = 0)
    (hrow5 : (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A - (1 : F) * D0 * d S0 -
        (2 : F) * C0 * d T0 - (3 : F) * B * d U0 -
        (4 : F) * A * d V0 - (6 : F) * d X0 = 0)
    (hrow4 : (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        (1 : F) * W0 * d A - (1 : F) * D0 * d T0 -
        (2 : F) * C0 * d U0 - (3 : F) * B * d V0 -
        (4 : F) * A * d W0 = 0)
    (hrow2 : (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        (1 : F) * W0 * d C0 - (1 : F) * D0 * d V0 -
        (2 : F) * C0 * d W0 - (3 : F) * B * d X0 = 0) :
    d (bridgeMuResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h36 : d (36 : F) = 0 := d.map_natCast 36
  have h72 : d (72 : F) = 0 := d.map_natCast 72
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h243 : d (243 : F) = 0 := d.map_natCast 243
  have h1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h56c : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h23 : d (2 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h2]
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h109 : d (10 / 9 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h9, h10]
  have h49 : d (4 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h4]
  have h772 : d (7 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h7]
  have h581 : d (5 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h5]
  have h736 : d (7 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h7]
  have h1027 : d (10 / 27 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h27, h10]
  have h572 : d (5 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h5]
  have h527 : d (5 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h5]
  have h427 : d (4 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h4]
  have h351296 : d (35 / 1296 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h1296, h35]
  have h20243 : d (20 / 243 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h243, h20]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h3128 : d (3 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h3]
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have h10n : d (10 : F) = 0 := d.map_natCast 10
  have h20n : d (20 : F) = 0 := d.map_natCast 20
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h35n : d (35 : F) = 0 := d.map_natCast 35
  have h64n : d (64 : F) = 0 := d.map_natCast 64
  have h256n : d (256 : F) = 0 := d.map_natCast 256
  have h385n : d (385 : F) = 0 := d.map_natCast 385
  have h432n : d (432 : F) = 0 := d.map_natCast 432
  have h729n : d (729 : F) = 0 := d.map_natCast 729
  have h31104n : d (31104 : F) = 0 := d.map_natCast 31104
  have h16f : d (1 / 6 : F) = 0 := by
    simp [Derivation.leibniz_inv, h6]
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3]
  have h18f : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h536 : d (5 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h5]
  have h827 : d (8 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h8]
  have h481 : d (4 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h4]
  have h38531104 : d (385 / 31104 : F) = 0 := by
    simp [Derivation.leibniz_div, h31104n, h385n]
  have h35432 : d (35 / 432 : F) = 0 := by
    simp [Derivation.leibniz_div, h432n, h35n]
  have h3256 : d (3 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h3]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h3]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64n, h9]
  have h35729 : d (35 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h35n]
  have h2081 : d (20 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h20n]
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have h15n : d (15 : F) = 0 := d.map_natCast 15
  have h70n : d (70 : F) = 0 := d.map_natCast 70
  have h216n : d (216 : F) = 0 := d.map_natCast 216
  have h6561n : d (6561 : F) = 0 := d.map_natCast 6561
  have h7776n : d (7776 : F) = 0 := d.map_natCast 7776
  have hx14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have hx19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_inv, h9]
  have hx59 : d (5 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h5]
  have hx5243 : d (5 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h5]
  have hx8729 : d (8 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h8]
  have hx932 : d (9 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h9]
  have hx1081 : d (10 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h10n]
  have hx15256 : d (15 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h15n]
  have hx35216 : d (35 / 216 : F) = 0 := by
    simp [Derivation.leibniz_div, h216n, h35n]
  have hx356561 : d (35 / 6561 : F) = 0 := by
    simp [Derivation.leibniz_div, h6561n, h35n]
  have hx70729 : d (70 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h70n]
  have hx3857776 : d (385 / 7776 : F) = 0 := by
    simp [Derivation.leibniz_div, h7776n, h385n]
  have hsqE : d (E0 * E0) = (2 : F) * E0 * d E0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcubC : d (C0 ^ 3) = (3 : F) * C0 ^ 2 * d C0 := by
    have h2C : d (C0 ^ 2) = (2 : F) * C0 * d C0 := by
      simpa [pow_two] using hsqC
    simp [pow_three, Derivation.leibniz, h2C]
    ring
  have hquarB : d (B ^ 4) = (4 : F) * B ^ 3 * d B := by
    have : B ^ 4 = B ^ 3 * B := by ring
    rw [this]
    simp [Derivation.leibniz, hcubB]
    ring
  have hsext : d (A ^ 6) = (6 : F) * A ^ 5 * d A := by
    have : A ^ 6 = A ^ 5 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquint]
    ring
  have hPderiv : d P = (5 / 3 : F) * d A := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 3 : F) * d B + (3 / 2 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
      simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hRderiv : d R = (5 / 3 : F) * d C0 + (3 / 2 : F) * L * d B +
      (4 / 3 : F) * P * d A - (10 / 9 : F) * A * d A := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma' + (-(4 / 3 : F) * A) * hPderiv.symm
  have hSderiv : d S0 = (5 / 3 : F) * d D0 + (3 / 2 : F) * L * d C0 +
      (4 / 3 : F) * P * d B - (10 / 9 : F) * A * d B +
      (7 / 6 : F) * Q * d A - (A * L + (5 / 6 : F) * B) * d A := by
    have hexp :
        deltaResidual610 L A B C0 D0 P Q S0 =
          S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
            (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
            (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
      simp only [deltaResidual610, alphaResidual610, betaResidual610,
        pow_two]
      ring
    have hdlt := hdelta
    rw [hexp] at hdlt
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h55 : d (55 : F) = 0 := d.map_natCast 55
    have h11 : d (11 : F) = 0 := d.map_natCast 11
    have h5518 : d (55 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h55]
    have h118 : d (11 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h11]
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h5518, h118, zero_mul, add_zero, mul_zero, hsq] at hdlt
    rw [hPderiv, hQderiv] at hdlt
    linear_combination hdlt
  have hTderiv : d T0 = (5 / 3 : F) * d E0 + (3 / 2 : F) * L * d D0 +
      (4 / 3 : F) * P * d C0 - (10 / 9 : F) * A * d C0 +
      (7 / 6 : F) * Q * d B - (A * L + (5 / 6 : F) * B) * d B +
      R * d A +
      ((20 / 27 : F) * A ^ 2 - (8 / 9 : F) * A * P - (3 / 4 : F) * L * B -
        (5 / 9 : F) * C0) * d A := by
    have hexp :
        epsilonResidual610 L A B C0 D0 E0 P Q R T0 =
          T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
            (4 / 3 : F) * P * C0 - (7 / 6 : F) * Q * B - R * A +
            (25 / 9 : F) * A * C0 + (25 / 18 : F) * (B * B) +
            (5 / 2 : F) * L * A * B + (10 / 9 : F) * P * (A * A) -
            (100 / 81 : F) * (A * A * A) := by
      simp only [epsilonResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, pow_two, pow_three]
      ring
    have heps := hepsilon
    rw [hexp] at heps
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h100 : d (100 : F) = 0 := d.map_natCast 100
    have h259 : d (25 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h25]
    have h2518 : d (25 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h25]
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h10081 : d (100 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h100]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h259, h2518, h52, h109, h10081, zero_mul, add_zero, mul_zero, hsq,
      hcub', hsqB] at heps
    rw [hPderiv, hQderiv, hRderiv] at heps
    linear_combination heps
  have hUderiv : d U0 =
      (3 / 2 : F) * L * d E0 +
        (4 / 3 : F) * P * d D0 + (4 / 3 : F) * D0 * d P +
        (7 / 6 : F) * Q * d C0 + (7 / 6 : F) * C0 * d Q +
        R * d B + B * d R +
        (5 / 6 : F) * S0 * d A + (5 / 6 : F) * A * d S0 -
        (5 / 2 : F) * A * d D0 - (5 / 2 : F) * D0 * d A -
        (5 / 2 : F) * B * d C0 - (5 / 2 : F) * C0 * d B -
        (2 : F) * A * B * d P - (2 : F) * A * P * d B -
        (2 : F) * B * P * d A -
        (7 / 8 : F) * (A * A) * d Q - (7 / 4 : F) * Q * A * d A -
        (9 / 4 : F) * L * A * d C0 - (9 / 4 : F) * L * C0 * d A -
        (9 / 4 : F) * L * B * d B +
        (25 / 8 : F) * (A * A) * d B + (25 / 4 : F) * A * B * d A +
        (45 / 16 : F) * L * (A * A) * d A := by
    have hexp :
        zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 =
          U0 - (3 / 2 : F) * L * E0 - (4 / 3 : F) * P * D0 -
            (7 / 6 : F) * Q * C0 - R * B - (5 / 6 : F) * S0 * A +
            (5 / 2 : F) * A * D0 + (5 / 2 : F) * B * C0 +
            (2 : F) * A * B * P + (7 / 8 : F) * Q * (A * A) +
            (9 / 4 : F) * L * A * C0 + (9 / 8 : F) * L * (B * B) -
            (25 / 8 : F) * (A * A) * B -
            (15 / 16 : F) * L * (A * A * A) := by
      simp only [zetaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, pow_two, pow_three]
      ring
    have hz := hzeta
    rw [hexp] at hz
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h78 : d (7 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h7]
    have h94 : d (9 / 4 : F) = 0 := by
      simp [Derivation.leibniz_div, h4, h9]
    have h98 : d (9 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h9]
    have h258 : d (25 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h25]
    have h16ne : (16 : F) ≠ 0 := by norm_num
    have h16inv : d (16 : F)⁻¹ = 0 := by
      have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
      have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
        rw [hone]
        exact d.map_one_eq_zero
      have hleib :
          d ((16 : F) * (16 : F)⁻¹) =
            (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
        Derivation.leibniz d (16 : F) (16 : F)⁻¹
      have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
        simpa [smul_eq_mul, hd1] using hleib.symm
      have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
        simpa [h16, mul_zero, add_zero] using hsum
      exact (mul_eq_zero.mp honly).resolve_left h16ne
    have h1516 : d (15 / 16 : F) = 0 := by
      simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
        add_zero, mul_zero]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h32, h43, h76, h56c, hL,
      h52, h78, h94, h98, h258, h1516, zero_mul, add_zero, mul_zero, hsq,
      hsqB, hcub', h2] at hz
    linear_combination hz
  have hVderiv : d V0 =
      (2 / 3 : F) * (d A * T0 + A * d T0) +
        (5 / 6 : F) * (d B * S0 + B * d S0) +
        (d C0 * R + C0 * d R) -
        (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) +
        (7 / 6 : F) * (d D0 * Q + D0 * d Q) -
        (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) +
        (4 / 3 : F) * (d E0 * P + E0 * d P) -
        (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) -
        (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) +
        (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
          (A * A * A) * d P) -
        (20 / 9 : F) * (d A * E0 + A * d E0) -
        (20 / 9 : F) * (d B * D0 + B * d D0) -
        (10 / 9 : F) * ((2 : F) * C0 * d C0) -
        (2 : F) * L * (d A * D0 + A * d D0) -
        (2 : F) * L * (d B * C0 + B * d C0) +
        (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) +
        (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) +
        (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) -
        (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
    have hexp :
        etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 =
          V0 - (2 / 3 : F) * A * T0 - (5 / 6 : F) * B * S0 - C0 * R +
            (2 / 3 : F) * (A * A) * R - (7 / 6 : F) * D0 * Q +
            (14 / 9 : F) * A * B * Q - (4 / 3 : F) * E0 * P +
            (16 / 9 : F) * A * C0 * P + (8 / 9 : F) * (B * B) * P -
            (56 / 81 : F) * (A * A * A) * P + (20 / 9 : F) * A * E0 +
            (20 / 9 : F) * B * D0 + (10 / 9 : F) * (C0 * C0) +
            (2 : F) * A * D0 * L + (2 : F) * B * C0 * L -
            (7 / 3 : F) * (A * A) * B * L - (70 / 27 : F) * (A * A) * C0 -
            (70 / 27 : F) * A * (B * B) +
            (175 / 243 : F) * (A * A * A * A) := by
      simp only [etaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, epsilonResidual610, pow_two,
        pow_three]
      ring
    have h14 : d (14 : F) = 0 := d.map_natCast 14
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    have h56 : d (56 : F) = 0 := d.map_natCast 56
    have h70 : d (70 : F) = 0 := d.map_natCast 70
    have h175 : d (175 : F) = 0 := d.map_natCast 175
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h149 : d (14 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h14]
    have h169 : d (16 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h16]
    have h89 : d (8 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h8]
    have h5681 : d (56 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h56]
    have h209 : d (20 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h20]
    have h73 : d (7 / 3 : F) = 0 := by
      simp [Derivation.leibniz_div, h3, h7]
    have h7027 : d (70 / 27 : F) = 0 := by
      simp [Derivation.leibniz_div, h27, h70]
    have h175243 : d (175 / 243 : F) = 0 := by
      simp [Derivation.leibniz_div, h243, h175]
    have h109' : d (10 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h10]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    have hquart : d (A * A * A * A) =
        (4 : F) * (A * A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    have hdAT : d ((2 / 3 : F) * A * T0) =
        (2 / 3 : F) * (d A * T0 + A * d T0) := by
      simp [Derivation.leibniz, smul_eq_mul, h23]
      ring
    have hdBS : d ((5 / 6 : F) * B * S0) =
        (5 / 6 : F) * (d B * S0 + B * d S0) := by
      simp [Derivation.leibniz, smul_eq_mul, h56c]
      ring
    have hdCR : d (C0 * R) = d C0 * R + C0 * d R := by
      simp [Derivation.leibniz, smul_eq_mul]
      ring
    have hdA2R : d ((2 / 3 : F) * (A * A) * R) =
        (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) := by
      simp [Derivation.leibniz, smul_eq_mul, h23, hsq]
      ring
    have hdDQ : d ((7 / 6 : F) * D0 * Q) =
        (7 / 6 : F) * (d D0 * Q + D0 * d Q) := by
      simp [Derivation.leibniz, smul_eq_mul, h76]
      ring
    have hdABQ : d ((14 / 9 : F) * A * B * Q) =
        (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) := by
      simp [Derivation.leibniz, smul_eq_mul, h149]
      ring
    have hdEP : d ((4 / 3 : F) * E0 * P) =
        (4 / 3 : F) * (d E0 * P + E0 * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h43]
      ring
    have hdACP : d ((16 / 9 : F) * A * C0 * P) =
        (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h169]
      ring
    have hdB2P : d ((8 / 9 : F) * (B * B) * P) =
        (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h89, hsqB]
      ring
    have hdA3P : d ((56 / 81 : F) * (A * A * A) * P) =
        (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
          (A * A * A) * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h5681, hcub']
      ring
    have hdAE : d ((20 / 9 : F) * A * E0) =
        (20 / 9 : F) * (d A * E0 + A * d E0) := by
      simp [Derivation.leibniz, smul_eq_mul, h209]
      ring
    have hdBD : d ((20 / 9 : F) * B * D0) =
        (20 / 9 : F) * (d B * D0 + B * d D0) := by
      simp [Derivation.leibniz, smul_eq_mul, h209]
      ring
    have hdC2 : d ((10 / 9 : F) * (C0 * C0)) =
        (10 / 9 : F) * ((2 : F) * C0 * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h109', hsqC]
      try ring
    have hdADL : d ((2 : F) * A * D0 * L) =
        (2 : F) * L * (d A * D0 + A * d D0) := by
      simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
      ring
    have hdBCL : d ((2 : F) * B * C0 * L) =
        (2 : F) * L * (d B * C0 + B * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
      ring
    have hdA2BL : d ((7 / 3 : F) * (A * A) * B * L) =
        (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) := by
      simp [Derivation.leibniz, smul_eq_mul, h73, hL, hsq, zero_mul,
        add_zero]
      ring
    have hdA2C : d ((70 / 27 : F) * (A * A) * C0) =
        (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h7027, hsq]
      ring
    have hdAB2 : d ((70 / 27 : F) * A * (B * B)) =
        (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) := by
      simp [Derivation.leibniz, smul_eq_mul, h7027, hsqB]
      ring
    have hdA4 : d ((175 / 243 : F) * (A * A * A * A)) =
        (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
      simp [Derivation.leibniz, smul_eq_mul, h175243, hquart]
      try ring
    have he := heta
    rw [hexp] at he
    simp only [map_sub, map_add, hdAT, hdBS, hdCR, hdA2R, hdDQ, hdABQ,
      hdEP, hdACP, hdB2P, hdA3P, hdAE, hdBD, hdC2, hdADL, hdBCL, hdA2BL,
      hdA2C, hdAB2, hdA4] at he
    linear_combination he

  have hWderiv :
      d W0 = (7 / 6 : F) * Q * d E0 + R * d D0 +
        (5 / 6 : F) * S0 * d C0 + (2 / 3 : F) * T0 * d B +
        (1 / 2 : F) * U0 * d A -
        (1 / 6 : F) * D0 * d R - (1 / 3 : F) * C0 * d S0 -
        (1 / 2 : F) * B * d T0 - (2 / 3 : F) * A * d U0 := by
    linear_combination (-1 / 6 : F) * hrow6
  have hXderiv :
      d X0 = R * d E0 + (5 / 6 : F) * S0 * d D0 +
        (2 / 3 : F) * T0 * d C0 + (1 / 2 : F) * U0 * d B +
        (1 / 3 : F) * V0 * d A -
        (1 / 6 : F) * D0 * d S0 - (1 / 3 : F) * C0 * d T0 -
        (1 / 2 : F) * B * d U0 - (2 / 3 : F) * A * d V0 := by
    linear_combination (-1 / 6 : F) * hrow5
  have hmn11 : d (11 : F) = 0 := d.map_natCast 11
  have hmn14 : d (14 : F) = 0 := d.map_natCast 14
  have hmn24 : d (24 : F) = 0 := d.map_natCast 24
  have hmn25 : d (25 : F) = 0 := d.map_natCast 25
  have hmn54 : d (54 : F) = 0 := d.map_natCast 54
  have hmn77 : d (77 : F) = 0 := d.map_natCast 77
  have hmn108 : d (108 : F) = 0 := d.map_natCast 108
  have hmn110 : d (110 : F) = 0 := d.map_natCast 110
  have hmn144 : d (144 : F) = 0 := d.map_natCast 144
  have hmn162 : d (162 : F) = 0 := d.map_natCast 162
  have hmn576 : d (576 : F) = 0 := d.map_natCast 576
  have hmn972 : d (972 : F) = 0 := d.map_natCast 972
  have hmn1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have hmn1458 : d (1458 : F) = 0 := d.map_natCast 1458
  have hmn3456 : d (3456 : F) = 0 := d.map_natCast 3456
  have hmn15552 : d (15552 : F) = 0 := d.map_natCast 15552
  have hmf1_24 : d (1 / 24 : F) = 0 := by
    simp [Derivation.leibniz_inv, hmn24]
  have hmf35_3456 : d (35 / 3456 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn3456, h35n]
  have hmf25_432 : d (25 / 432 : F) = 0 := by
    simp [Derivation.leibniz_div, h432n, hmn25]
  have hmf77_15552 : d (77 / 15552 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn15552, hmn77]
  have hmf35_972 : d (35 / 972 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn972, h35n]
  have hmf35_576 : d (35 / 576 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn576, h35n]
  have hmf7_144 : d (7 / 144 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn144, h7]
  have hmf7_54 : d (7 / 54 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn54, h7]
  have hmf7_108 : d (7 / 108 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn108, h7]
  have hmf10_243 : d (10 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h10n]
  have hmf14_243 : d (14 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, hmn14]
  have hmf16_81 : d (16 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h16]
  have hmf2_27 : d (2 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h2]
  have hmf5_1024 : d (5 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn1024, h5]
  have hmf11_256 : d (11 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, hmn11]
  have hmf1_16 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have hmf7_32 : d (7 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h7]
  have hmf7_64 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64n, h7]
  have hmf35_1458 : d (35 / 1458 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn1458, h35n]
  have hmf25_729 : d (25 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, hmn25]
  have hmf110_729 : d (110 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, hmn110]
  have hmf35_162 : d (35 / 162 : F) = 0 := by
    simp [Derivation.leibniz_div, hmn162, h35n]
  have hrow2_red := hrow2
  simp only [hXderiv, hWderiv, hPderiv, hQderiv, hRderiv, hSderiv,
    hTderiv, hUderiv, hVderiv] at hrow2_red
  have hrow4_red := hrow4
  simp only [hXderiv, hWderiv, hPderiv, hQderiv, hRderiv, hSderiv,
    hTderiv, hUderiv, hVderiv] at hrow4_red
  simp only [bridgeMuResidual610, map_sub, map_add, map_neg, Derivation.leibniz,
    smul_eq_mul, h16f, h13, h12, hx14, hx19, h23, h29, h34, h38, h316,
    h332, h49, h427, h481, hx59, h527, h536, h572, h581, hx5243, h736,
    h772, h827, hx8729, hx932, h1027, hx1081, hx15256, h2081, h20243,
    hx35216, h35432, h35729, h351296, hx356561, hx70729, hx3857776,
    h3128, h18f,
    hmf1_24, hmf35_3456, hmf25_432, hmf77_15552, hmf35_972, hmf35_576, hmf7_144, hmf7_54, hmf7_108, hmf10_243, hmf14_243, hmf16_81, hmf2_27, hmf5_1024, hmf11_256, hmf1_16, hmf7_32, hmf7_64, hmf35_1458, hmf25_729, hmf110_729, hmf35_162,
    hL, halpha,
    hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta, hsq, hsqB,
    hsqC, hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint, hsext,
    pow_two, pow_three, zero_mul, add_zero, mul_zero]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610, pow_two, pow_three]
  linear_combination (1 / 6 : F) * hrow2_red - (1 / 12 : F) * A * hrow4_red

end BridgeMuDepressedRow610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`59` head. -/
theorem bridgeMuJetHead610_eval
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 : k[X]) (lambda : k) (x : k) :
    (bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
        (Polynomial.C lambda)).eval x =
      bridgeMuJetHead610 (w1.eval x) (a41.eval x) (p32.eval x)
        (s1.eval x) (u2.eval x) (b62.eval x) (q53.eval x)
        (p2.eval x) (q41.eval x) (q3.eval x) lambda := by
  simp only [bridgeMuJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C]

end BridgeMuJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`61` deep head. -/
theorem bridgeMuDeepHead610_eval
    (w1 p32 u2 b63 p21 q42 q31 : k[X]) (lambda : k) (x : k) :
    (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
        (Polynomial.C lambda)).eval x =
      bridgeMuDeepHead610 (w1.eval x) (p32.eval x) (u2.eval x)
        (b63.eval x) (p21.eval x) (q42.eval x) (q31.eval x)
        lambda := by
  simp only [bridgeMuDeepHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C]

end BridgeMuJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`59` head modulo
`3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load alone. -/
theorem bridgeMu_chamberFreeReduction610
    (w1 a41 p32 s1 u2 b62 q53 p2 q41 q3 lam : F)
    (hhead : bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
      lam = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0) :
    - (1120 : F) * a41 ^ 6 * w1
    + (189 : F) * a41 ^ 6 * lam
    + (220 : F) * a41 ^ 5 * p32
    + (588 : F) * a41 ^ 5 * u2
    + (9200 : F) * a41 ^ 4 * p2 * w1
    - (1260 : F) * a41 ^ 4 * p2 * lam
    - (600 : F) * a41 ^ 4 * q53
    - (3360 : F) * a41 ^ 3 * p2 * p32
    - (3360 : F) * a41 ^ 3 * p2 * u2
    - (1920 : F) * a41 ^ 3 * q41 * w1
    + (576 : F) * a41 ^ 3 * q3
    - (17280 : F) * a41 ^ 2 * p2 ^ 2 * w1
    + (2160 : F) * a41 ^ 2 * p2 ^ 2 * lam
    + (2880 : F) * a41 ^ 2 * p2 * q53
    + (2304 : F) * a41 ^ 2 * p32 * q41
    + (4800 : F) * a41 * p2 ^ 2 * p32
    + (4032 : F) * a41 * p2 ^ 2 * u2
    + (4608 : F) * a41 * p2 * q41 * w1
    - (2304 : F) * a41 * p2 * q3
    + (3840 : F) * p2 ^ 3 * w1
    - (576 : F) * p2 ^ 3 * lam
    - (1920 : F) * p2 ^ 2 * q53
    - (3072 : F) * p2 * p32 * q41 = 0 := by
  simp only [bridgeMuJetHead610] at hhead
  linear_combination (3 / 4096 : F) * hhead +
    ((1008 : F) * a41 ^ 5 * w1 - (1120 : F) * a41 ^ 4 * p32 -
      (4480 : F) * a41 ^ 3 * p2 * w1 + (3840 : F) * a41 ^ 2 * p2 * p32 +
      (3840 : F) * a41 * p2 ^ 2 * w1 - (1536 : F) * p2 ^ 2 * p32) * hs +
    ((140 : F) * a41 ^ 4 * w1 - (160 : F) * a41 ^ 3 * p32 -
      (480 : F) * a41 ^ 2 * p2 * w1 + (384 : F) * a41 * p2 * p32 +
      (192 : F) * p2 ^ 2 * w1) * hU

end BridgeMuScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeMuScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- On the collapsed sibling child the vanishing order-`61` deep head
factors as `p₃₂` times its cofactor — the honest split `p₃₂ = 0`
(whence `u₂ = 0` through the retained tie) or the first `λ`-loaded
tie on the quotient jet. -/
theorem bridgeMu_siblingDeepSplit610
    (w1 p32 u2 b63 p21 q42 q31 lam : F)
    (hhead : bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31 lam = 0)
    (htie : (3 : F) * u2 = (5 : F) * p32) :
    (p32 = 0 ∧ u2 = 0) ∨
      (45 : F) * lam * p32 ^ 3 + (144 : F) * b63 * p32 ^ 2 +
          (240 : F) * p21 * p32 ^ 2 + (288 : F) * p32 * q42 * w1 -
        (400 : F) * p32 ^ 3 * w1 - (144 : F) * p32 * q31 -
          (384 : F) * p21 * q42 = 0 := by
  simp only [bridgeMuDeepHead610] at hhead
  have hprod : p32 *
      ((100 : F) * p32 ^ 3 * w1 + (15 : F) * p32 ^ 3 * lam +
        (48 : F) * p32 ^ 2 * b63 - (200 : F) * p32 ^ 2 * p21 -
        (140 : F) * p32 ^ 2 * u2 * w1 + (168 : F) * p32 * p21 * u2 +
        (96 : F) * p32 * q42 * w1 - (48 : F) * p32 * q31 -
        (128 : F) * p21 * q42) = 0 := by
    linear_combination (1 / 32768 : F) * hhead
  rcases mul_eq_zero.mp hprod with hp32z | hF
  · left
    refine ⟨hp32z, ?_⟩
    linear_combination (1 / 3 : F) * htie + (5 / 3 : F) * hp32z
  · right
    linear_combination (3 : F) * hF +
      (-(168 : F) * p21 * p32 + (140 : F) * p32 ^ 2 * w1) * htie

end BridgeMuScalars610

end Max11DegreeRoutes
