import Fable610ScaleTwoKappaIntegralBridgeCompatScratch

/-! # Lambda integral bridge continuation for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h₀²` and `N = 5 p₅ H² - 3 q₉ = λ h₀⁹`
with `h₀.natDegree = 1`, the compatible `κ` bridge spent the degree-`4`
first integral; the next genuinely unused integral row is the
degree-`3` first integral, whose `X'` derivative is eliminated through
the degree-`5` row, so its construction uses only the second- through
ninth-face integrals already on this chain together with the
degree-`3` depressed row restated here.  The scale-zero eleventh
defect scratch states this row at constant scale but collides with the
canonical scale-two declarations, so nothing is imported from it: this
file restates on the compatible scale-two chain the degree-`3`
residual, its derivation-in-zero reduction, and the weight-`60`
clearing `bridgeClearedLambdaDefect610 = C lambdaNu · h₀⁶⁰`, derived
from the source differential rows already in the canonical ancestry
(rows `13` through `7`, the bridge rows `6` and `5`, and the
degree-`3` row restated here).  The spent `ι` and `κ` packets are
reused opaquely; neither weight-`50` nor weight-`55` numerator is ever
re-expanded.

On the fifteenth-face jet `p₅ = h₀⁵ w₁`, `p₄ = h₀³ a₄₁`,
`p₃ = h₀ p₃₁`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁵ u₁`, `q₆ = h₀⁴ b₆₂`,
`q₅ = h₀² q₅₂` the numerator factors exactly through `h₀⁵²`, eight
orders below the defect weight, with fully factored head
`531441 p₃₁² (105 p₃₁ u₁ - 100 p₃₁² - 108 q₄)`; the peel is
`head + h₀ · tail = C lambdaNu · h₀⁸`, so the head vanishes at the
root, and modulo the chamber-free tenth-face root laws `3 u₁ = 5 p₃₁`
and `9 q₄ = 5 p₃₁²` alone it reduces to `7971615 p₃₁(a)⁴ = 0` — the
chamber-free kill `p₃₁(a) = 0`, a relation the `ι` and `κ` heads never
reached.  The `p₃₁(a) ≠ 0` complement child of the terminal closure is
eliminated by honest contradiction, and the deeper divisibilities
`p₃ = h₀² p₃₂`, `q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`, `q₄ = h₀ q₄₁` formerly
confined to the sibling child now hold globally, merging both towers.

Substituting the merged jet peels the same weight-`60` defect one
order further: `deepHead + h₀ · deepTail = C lambdaNu · h₀⁶` with the
order-`54` head vanishing at the root; modulo `3 s₁ = 5 a₄₁` and the
`p₃₁`-killed `U`-load `10 a₄₁² - 18 b₆₂ + 30 p₂ = 0` it reduces,
chamber-free, to `100 a₄₁⁶ - 1575 a₄₁⁴ p₂ + 810 a₄₁³ q₄₁
+ 4860 a₄₁² p₂² - 2916 a₄₁ p₂ q₄₁ - 1620 p₂³ = 0`.  On the sibling
child the retained tie `81 q₄₁ = 90 a₄₁ p₂ - 5 a₄₁³` reduces this to
`10 a₄₁⁶ - 99 a₄₁⁴ p₂ + 324 a₄₁² p₂² - 324 p₂³ = 0`; its
`a₄₁(a) = 0` branch forces `p₂(a) = 0` outright, and on the quartic
branch the resultant certificate `(52 a₄₁² - 2543 p₂) f
+ (-130 a₄₁⁴ + 6507 a₄₁² p₂ - 7290 p₂²) g = 167832 p₂⁴` forces
`p₂(a) = 0` and then `a₄₁(a) = 0`, so the sibling child collapses to
`a₄₁(a) = p₂(a) = 0` with the cascade `s₁(a) = b₆₂(a) = q₄₁(a)
= q₅₃(a) = q₃(a) = 0` and the self-similar tie `3 u₂(a) = 5 p₃₂(a)`.
On the pinned complement child `6 p₂ = a₄₁²`, `6 b₆₂ = 5 a₄₁²` the
relation factors as `a₄₁³ (324 q₄₁ - 35 a₄₁³) = 0` — the honest split
`a₄₁(a) = 0` (whence `p₂(a) = b₆₂(a) = 0`) or the new pin
`324 q₄₁(a) = 35 a₄₁(a)³`, the first `q`-jet pin on that child.

Neither surviving child is closed, because neither is contradicted —
the inhomogeneous Keller boundary row `p₀'(a) q₁(a) - p₁(a) q₀'(a)
= j ≠ 0` lives on the fresh coordinates `p₀, p₁, q₀, q₁` the `h`-adic
jet does not control.  The honest residual is that single boundary
relation, the two refined `p₃₁(a) = 0` children, the preserved ground
constants `ζ, η, iotaK, kappaMu, lambdaNu`, and the open aligned face
`N = 0`.  The next unused integral row is the degree-`2` first
integral; the next unused aligned row on `N = 0` is the degree-`10`
row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Degree-`3` residual and its weight-`60` clearing -/

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

set_option maxHeartbeats 8000000 in
/-- Polynomial numerator of `258280326 h⁶⁰ λ` on the ninth-power face. -/
def bridgeClearedLambdaDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    (8107385 : F[X]) * a5 ^ 12
    - (3979989 : F[X]) * a5 ^ 11 * h ^ 5 * Polynomial.C lambda
    - (80514720 : F[X]) * a4 * a5 ^ 10 * h ^ 6
    - (12077208 : F[X]) * a5 ^ 10 * b8 * h ^ 2
    + (84192075 : F[X]) * a3 * a5 ^ 9 * h ^ 12
    + (45289530 : F[X]) * a4 * a5 ^ 9 * h ^ 11 * Polynomial.C lambda
    + (12193335 : F[X]) * a5 ^ 9 * b7 * h ^ 8
    - (88609950 : F[X]) * a2 * a5 ^ 8 * h ^ 18
    - (47031435 : F[X]) * a3 * a5 ^ 8 * h ^ 17 * Polynomial.C lambda
    + (261285750 : F[X]) * a4 ^ 2 * a5 ^ 8 * h ^ 12
    + (125417160 : F[X]) * a4 * a5 ^ 8 * b8 * h ^ 8
    - (12269070 : F[X]) * a5 ^ 8 * b6 * h ^ 14
    + (94062870 : F[X]) * a1 * a5 ^ 7 * h ^ 24
    + (49076280 : F[X]) * a2 * a5 ^ 7 * h ^ 23 * Polynomial.C lambda
    - (463498200 : F[X]) * a3 * a4 * a5 ^ 7 * h ^ 18
    - (130870080 : F[X]) * a3 * a5 ^ 7 * b8 * h ^ 14
    - (188125740 : F[X]) * a4 ^ 2 * a5 ^ 7 * h ^ 17 * Polynomial.C lambda
    - (114511320 : F[X]) * a4 * a5 ^ 7 * b7 * h ^ 14
    + (12269070 : F[X]) * a5 ^ 7 * b5 * h ^ 20
    - (101039400 : F[X]) * a0 * a5 ^ 6 * h ^ 30
    - (51530094 : F[X]) * a1 * a5 ^ 6 * h ^ 29 * Polynomial.C lambda
    + (400789620 : F[X]) * a2 * a4 * a5 ^ 6 * h ^ 24
    + (137413584 : F[X]) * a2 * a5 ^ 6 * b8 * h ^ 20
    + (200394810 : F[X]) * a3 ^ 2 * a5 ^ 6 * h ^ 24
    + (343533960 : F[X]) * a3 * a4 * a5 ^ 6 * h ^ 23 * Polynomial.C lambda
    + (120236886 : F[X]) * a3 * a5 ^ 6 * b7 * h ^ 20
    - (254469600 : F[X]) * a4 ^ 3 * a5 ^ 6 * h ^ 18
    - (458045280 : F[X]) * a4 ^ 2 * a5 ^ 6 * b8 * h ^ 14
    + (103060188 : F[X]) * a4 * a5 ^ 6 * b6 * h ^ 20
    - (12124728 : F[X]) * a5 ^ 6 * b4 * h ^ 26
    + (54561276 : F[X]) * a0 * a5 ^ 5 * h ^ 35 * Polynomial.C lambda
    - (333430020 : F[X]) * a1 * a4 * a5 ^ 5 * h ^ 30
    - (145496736 : F[X]) * a1 * a5 ^ 5 * b8 * h ^ 26
    - (333430020 : F[X]) * a2 * a3 * a5 ^ 5 * h ^ 30
    - (309180564 : F[X]) * a2 * a4 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    - (127309644 : F[X]) * a2 * a5 ^ 5 * b7 * h ^ 26
    - (154590282 : F[X]) * a3 ^ 2 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    + (429417450 : F[X]) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 24
    + (824481504 : F[X]) * a3 * a4 * a5 ^ 5 * b8 * h ^ 20
    - (109122552 : F[X]) * a3 * a5 ^ 5 * b6 * h ^ 26
    + (343533960 : F[X]) * a4 ^ 3 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    + (360710658 : F[X]) * a4 ^ 2 * a5 ^ 5 * b7 * h ^ 20
    - (90935460 : F[X]) * a4 * a5 ^ 5 * b5 * h ^ 26
    + (11691702 : F[X]) * a5 ^ 5 * b3 * h ^ 32
    + (259815600 : F[X]) * a0 * a4 * a5 ^ 4 * h ^ 36
    + (155889360 : F[X]) * a0 * a5 ^ 4 * b8 * h ^ 32
    + (259815600 : F[X]) * a1 * a3 * a5 ^ 4 * h ^ 36
    + (272806380 : F[X]) * a1 * a4 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    + (136403190 : F[X]) * a1 * a5 ^ 4 * b7 * h ^ 32
    + (129907800 : F[X]) * a2 ^ 2 * a5 ^ 4 * h ^ 36
    + (272806380 : F[X]) * a2 * a3 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (151559100 : F[X]) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 30
    - (727483680 : F[X]) * a2 * a4 * a5 ^ 4 * b8 * h ^ 26
    + (116917020 : F[X]) * a2 * a5 ^ 4 * b6 * h ^ 32
    - (151559100 : F[X]) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 30
    - (363741840 : F[X]) * a3 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (772951410 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    - (636548220 : F[X]) * a3 * a4 * a5 ^ 4 * b7 * h ^ 26
    + (97430850 : F[X]) * a3 * a5 ^ 4 * b5 * h ^ 32
    - (143139150 : F[X]) * a4 ^ 4 * a5 ^ 4 * h ^ 24
    + (687067920 : F[X]) * a4 ^ 3 * a5 ^ 4 * b8 * h ^ 20
    - (272806380 : F[X]) * a4 ^ 2 * a5 ^ 4 * b6 * h ^ 26
    + (77944680 : F[X]) * a4 * a5 ^ 4 * b4 * h ^ 32
    - (10628820 : F[X]) * a5 ^ 4 * b2 * h ^ 38
    - (177147000 : F[X]) * a0 * a3 * a5 ^ 3 * h ^ 42
    - (233834040 : F[X]) * a0 * a4 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (148803480 : F[X]) * a0 * a5 ^ 3 * b7 * h ^ 38
    - (177147000 : F[X]) * a1 * a2 * a5 ^ 3 * h ^ 42
    - (233834040 : F[X]) * a1 * a3 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (64953900 : F[X]) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    + (623557440 : F[X]) * a1 * a4 * a5 ^ 3 * b8 * h ^ 32
    - (127545840 : F[X]) * a1 * a5 ^ 3 * b6 * h ^ 38
    - (116917020 : F[X]) * a2 ^ 2 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (129907800 : F[X]) * a2 * a3 * a4 * a5 ^ 3 * h ^ 36
    + (623557440 : F[X]) * a2 * a3 * a5 ^ 3 * b8 * h ^ 32
    + (545612760 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (545612760 : F[X]) * a2 * a4 * a5 ^ 3 * b7 * h ^ 32
    - (106288200 : F[X]) * a2 * a5 ^ 3 * b5 * h ^ 38
    - (21651300 : F[X]) * a3 ^ 3 * a5 ^ 3 * h ^ 36
    + (545612760 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (272806380 : F[X]) * a3 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (707275800 : F[X]) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 30
    - (1454967360 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    + (467668080 : F[X]) * a3 * a4 * a5 ^ 3 * b6 * h ^ 32
    - (85030560 : F[X]) * a3 * a5 ^ 3 * b4 * h ^ 38
    - (257650470 : F[X]) * a4 ^ 4 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    - (424365480 : F[X]) * a4 ^ 3 * a5 ^ 3 * b7 * h ^ 26
    + (194861700 : F[X]) * a4 ^ 2 * a5 ^ 3 * b5 * h ^ 32
    - (63772920 : F[X]) * a4 * a5 ^ 3 * b3 * h ^ 38
    + (7971615 : F[X]) * a5 ^ 3 * b1 * h ^ 44
    + (79716150 : F[X]) * a0 * a2 * a5 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a0 * a3 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (212576400 : F[X]) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a0 * a4 * a5 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a0 * a5 ^ 2 * b6 * h ^ 44
    + (39858075 : F[X]) * a1 ^ 2 * a5 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a1 * a2 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (425152800 : F[X]) * a1 * a3 * a4 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a1 * a3 * a5 ^ 2 * b8 * h ^ 38
    - (350751060 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a1 * a4 * a5 ^ 2 * b7 * h ^ 38
    + (119574225 : F[X]) * a1 * a5 ^ 2 * b5 * h ^ 44
    + (212576400 : F[X]) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 42
    - (255091680 : F[X]) * a2 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    + (212576400 : F[X]) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 42
    - (701502120 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a2 * a3 * a5 ^ 2 * b7 * h ^ 38
    - (649539000 : F[X]) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 32
    - (382637520 : F[X]) * a2 * a4 * a5 ^ 2 * b6 * h ^ 38
    + (95659380 : F[X]) * a2 * a5 ^ 2 * b4 * h ^ 44
    - (116917020 : F[X]) * a3 ^ 3 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (974308500 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * h ^ 32
    - (191318760 : F[X]) * a3 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    + (545612760 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (818419140 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (318864600 : F[X]) * a3 * a4 * a5 ^ 2 * b5 * h ^ 38
    + (71744535 : F[X]) * a3 * a5 ^ 2 * b3 * h ^ 44
    + (242494560 : F[X]) * a4 ^ 5 * a5 ^ 2 * h ^ 30
    - (363741840 : F[X]) * a4 ^ 4 * a5 ^ 2 * b8 * h ^ 26
    + (233834040 : F[X]) * a4 ^ 3 * a5 ^ 2 * b6 * h ^ 32
    - (127545840 : F[X]) * a4 ^ 2 * a5 ^ 2 * b4 * h ^ 38
    + (47829690 : F[X]) * a4 * a5 ^ 2 * b2 * h ^ 44
    + (47829690 : F[X]) * a0 * a1 * a5 * h ^ 54
    - (143489070 : F[X]) * a0 * a2 * a5 * h ^ 53 * Polynomial.C lambda
    - (558013050 : F[X]) * a0 * a3 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a0 * a3 * a5 * b8 * h ^ 44
    + (191318760 : F[X]) * a0 * a4 ^ 2 * a5 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a0 * a4 * a5 * b7 * h ^ 44
    - (143489070 : F[X]) * a0 * a5 * b5 * h ^ 50
    - (71744535 : F[X]) * a1 ^ 2 * a5 * h ^ 53 * Polynomial.C lambda
    - (558013050 : F[X]) * a1 * a2 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a1 * a2 * a5 * b8 * h ^ 44
    - (279006525 : F[X]) * a1 * a3 ^ 2 * a5 * h ^ 48
    + (382637520 : F[X]) * a1 * a3 * a4 * a5 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a1 * a3 * a5 * b7 * h ^ 44
    + (460582200 : F[X]) * a1 * a4 ^ 3 * a5 * h ^ 42
    - (510183360 : F[X]) * a1 * a4 ^ 2 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a1 * a4 * a5 * b6 * h ^ 44
    - (114791256 : F[X]) * a1 * a5 * b4 * h ^ 50
    - (279006525 : F[X]) * a2 ^ 2 * a3 * a5 * h ^ 48
    + (191318760 : F[X]) * a2 ^ 2 * a4 * a5 * h ^ 47 * Polynomial.C lambda
    + (167403915 : F[X]) * a2 ^ 2 * a5 * b7 * h ^ 44
    + (191318760 : F[X]) * a2 * a3 ^ 2 * a5 * h ^ 47 * Polynomial.C lambda
    + (1381746600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 * h ^ 42
    - (1020366720 : F[X]) * a2 * a3 * a4 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a2 * a3 * a5 * b6 * h ^ 44
    - (233834040 : F[X]) * a2 * a4 ^ 3 * a5 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a2 * a4 ^ 2 * a5 * b7 * h ^ 38
    + (239148450 : F[X]) * a2 * a4 * a5 * b5 * h ^ 44
    - (86093442 : F[X]) * a2 * a5 * b3 * h ^ 50
    + (460582200 : F[X]) * a3 ^ 3 * a4 * a5 * h ^ 42
    - (170061120 : F[X]) * a3 ^ 3 * a5 * b8 * h ^ 38
    - (350751060 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a3 ^ 2 * a4 * a5 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 ^ 2 * a5 * b5 * h ^ 44
    - (617062050 : F[X]) * a3 * a4 ^ 4 * a5 * h ^ 36
    + (623557440 : F[X]) * a3 * a4 ^ 3 * a5 * b8 * h ^ 32
    - (382637520 : F[X]) * a3 * a4 ^ 2 * a5 * b6 * h ^ 38
    + (191318760 : F[X]) * a3 * a4 * a5 * b4 * h ^ 44
    - (57395628 : F[X]) * a3 * a5 * b2 * h ^ 50
    + (54561276 : F[X]) * a4 ^ 5 * a5 * h ^ 35 * Polynomial.C lambda
    + (136403190 : F[X]) * a4 ^ 4 * a5 * b7 * h ^ 32
    - (106288200 : F[X]) * a4 ^ 3 * a5 * b5 * h ^ 38
    + (71744535 : F[X]) * a4 ^ 2 * a5 * b3 * h ^ 44
    - (28697814 : F[X]) * a4 * a5 * b1 * h ^ 50
    - (143489070 : F[X]) * a0 ^ 2 * h ^ 60
    + (86093442 : F[X]) * a0 * a1 * h ^ 59 * Polynomial.C lambda
    + (478296900 : F[X]) * a0 * a2 * a4 * h ^ 54
    - (229582512 : F[X]) * a0 * a2 * b8 * h ^ 50
    + (239148450 : F[X]) * a0 * a3 ^ 2 * h ^ 54
    - (143489070 : F[X]) * a0 * a3 * a4 * h ^ 53 * Polynomial.C lambda
    - (200884698 : F[X]) * a0 * a3 * b7 * h ^ 50
    - (212576400 : F[X]) * a0 * a4 ^ 3 * h ^ 48
    + (191318760 : F[X]) * a0 * a4 ^ 2 * b8 * h ^ 44
    - (172186884 : F[X]) * a0 * a4 * b6 * h ^ 50
    + (172186884 : F[X]) * a0 * b4 * h ^ 56
    + (239148450 : F[X]) * a1 ^ 2 * a4 * h ^ 54
    - (114791256 : F[X]) * a1 ^ 2 * b8 * h ^ 50
    + (478296900 : F[X]) * a1 * a2 * a3 * h ^ 54
    - (143489070 : F[X]) * a1 * a2 * a4 * h ^ 53 * Polynomial.C lambda
    - (200884698 : F[X]) * a1 * a2 * b7 * h ^ 50
    - (71744535 : F[X]) * a1 * a3 ^ 2 * h ^ 53 * Polynomial.C lambda
    - (637729200 : F[X]) * a1 * a3 * a4 ^ 2 * h ^ 48
    + (382637520 : F[X]) * a1 * a3 * a4 * b8 * h ^ 44
    - (172186884 : F[X]) * a1 * a3 * b6 * h ^ 50
    + (63772920 : F[X]) * a1 * a4 ^ 3 * h ^ 47 * Polynomial.C lambda
    + (167403915 : F[X]) * a1 * a4 ^ 2 * b7 * h ^ 44
    - (143489070 : F[X]) * a1 * a4 * b5 * h ^ 50
    + (129140163 : F[X]) * a1 * b3 * h ^ 56
    + (79716150 : F[X]) * a2 ^ 3 * h ^ 54
    - (71744535 : F[X]) * a2 ^ 2 * a3 * h ^ 53 * Polynomial.C lambda
    - (318864600 : F[X]) * a2 ^ 2 * a4 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a2 ^ 2 * a4 * b8 * h ^ 44
    - (86093442 : F[X]) * a2 ^ 2 * b6 * h ^ 50
    - (637729200 : F[X]) * a2 * a3 ^ 2 * a4 * h ^ 48
    + (191318760 : F[X]) * a2 * a3 ^ 2 * b8 * h ^ 44
    + (191318760 : F[X]) * a2 * a3 * a4 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a2 * a3 * a4 * b7 * h ^ 44
    - (143489070 : F[X]) * a2 * a3 * b5 * h ^ 50
    + (194861700 : F[X]) * a2 * a4 ^ 4 * h ^ 42
    - (170061120 : F[X]) * a2 * a4 ^ 3 * b8 * h ^ 38
    + (143489070 : F[X]) * a2 * a4 ^ 2 * b6 * h ^ 44
    - (114791256 : F[X]) * a2 * a4 * b4 * h ^ 50
    + (86093442 : F[X]) * a2 * b2 * h ^ 56
    - (53144100 : F[X]) * a3 ^ 4 * h ^ 48
    + (63772920 : F[X]) * a3 ^ 3 * a4 * h ^ 47 * Polynomial.C lambda
    + (55801305 : F[X]) * a3 ^ 3 * b7 * h ^ 44
    + (389723400 : F[X]) * a3 ^ 2 * a4 ^ 3 * h ^ 42
    - (255091680 : F[X]) * a3 ^ 2 * a4 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a3 ^ 2 * a4 * b6 * h ^ 44
    - (57395628 : F[X]) * a3 ^ 2 * b4 * h ^ 50
    - (58458510 : F[X]) * a3 * a4 ^ 4 * h ^ 41 * Polynomial.C lambda
    - (148803480 : F[X]) * a3 * a4 ^ 3 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 * a4 ^ 2 * b5 * h ^ 44
    - (86093442 : F[X]) * a3 * a4 * b3 * h ^ 50
    + (43046721 : F[X]) * a3 * b1 * h ^ 56
    - (30311820 : F[X]) * a4 ^ 6 * h ^ 36
    + (31177872 : F[X]) * a4 ^ 5 * b8 * h ^ 32
    - (31886460 : F[X]) * a4 ^ 4 * b6 * h ^ 38
    + (31886460 : F[X]) * a4 ^ 3 * b4 * h ^ 44
    - (28697814 : F[X]) * a4 ^ 2 * b2 * h ^ 50

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral `λ` of the degree-`3` row against `h⁶⁰`
on the ninth-power face. -/
theorem bridgeLambdaDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (258280326 : F) * h ^ 60 *
        bridgeLambdaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4)
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) =
    (8107385 : F) * a5 ^ 12
    - (3979989 : F) * a5 ^ 11 * h ^ 5 * lambda
    - (80514720 : F) * a4 * a5 ^ 10 * h ^ 6
    - (12077208 : F) * a5 ^ 10 * b8 * h ^ 2
    + (84192075 : F) * a3 * a5 ^ 9 * h ^ 12
    + (45289530 : F) * a4 * a5 ^ 9 * h ^ 11 * lambda
    + (12193335 : F) * a5 ^ 9 * b7 * h ^ 8
    - (88609950 : F) * a2 * a5 ^ 8 * h ^ 18
    - (47031435 : F) * a3 * a5 ^ 8 * h ^ 17 * lambda
    + (261285750 : F) * a4 ^ 2 * a5 ^ 8 * h ^ 12
    + (125417160 : F) * a4 * a5 ^ 8 * b8 * h ^ 8
    - (12269070 : F) * a5 ^ 8 * b6 * h ^ 14
    + (94062870 : F) * a1 * a5 ^ 7 * h ^ 24
    + (49076280 : F) * a2 * a5 ^ 7 * h ^ 23 * lambda
    - (463498200 : F) * a3 * a4 * a5 ^ 7 * h ^ 18
    - (130870080 : F) * a3 * a5 ^ 7 * b8 * h ^ 14
    - (188125740 : F) * a4 ^ 2 * a5 ^ 7 * h ^ 17 * lambda
    - (114511320 : F) * a4 * a5 ^ 7 * b7 * h ^ 14
    + (12269070 : F) * a5 ^ 7 * b5 * h ^ 20
    - (101039400 : F) * a0 * a5 ^ 6 * h ^ 30
    - (51530094 : F) * a1 * a5 ^ 6 * h ^ 29 * lambda
    + (400789620 : F) * a2 * a4 * a5 ^ 6 * h ^ 24
    + (137413584 : F) * a2 * a5 ^ 6 * b8 * h ^ 20
    + (200394810 : F) * a3 ^ 2 * a5 ^ 6 * h ^ 24
    + (343533960 : F) * a3 * a4 * a5 ^ 6 * h ^ 23 * lambda
    + (120236886 : F) * a3 * a5 ^ 6 * b7 * h ^ 20
    - (254469600 : F) * a4 ^ 3 * a5 ^ 6 * h ^ 18
    - (458045280 : F) * a4 ^ 2 * a5 ^ 6 * b8 * h ^ 14
    + (103060188 : F) * a4 * a5 ^ 6 * b6 * h ^ 20
    - (12124728 : F) * a5 ^ 6 * b4 * h ^ 26
    + (54561276 : F) * a0 * a5 ^ 5 * h ^ 35 * lambda
    - (333430020 : F) * a1 * a4 * a5 ^ 5 * h ^ 30
    - (145496736 : F) * a1 * a5 ^ 5 * b8 * h ^ 26
    - (333430020 : F) * a2 * a3 * a5 ^ 5 * h ^ 30
    - (309180564 : F) * a2 * a4 * a5 ^ 5 * h ^ 29 * lambda
    - (127309644 : F) * a2 * a5 ^ 5 * b7 * h ^ 26
    - (154590282 : F) * a3 ^ 2 * a5 ^ 5 * h ^ 29 * lambda
    + (429417450 : F) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 24
    + (824481504 : F) * a3 * a4 * a5 ^ 5 * b8 * h ^ 20
    - (109122552 : F) * a3 * a5 ^ 5 * b6 * h ^ 26
    + (343533960 : F) * a4 ^ 3 * a5 ^ 5 * h ^ 23 * lambda
    + (360710658 : F) * a4 ^ 2 * a5 ^ 5 * b7 * h ^ 20
    - (90935460 : F) * a4 * a5 ^ 5 * b5 * h ^ 26
    + (11691702 : F) * a5 ^ 5 * b3 * h ^ 32
    + (259815600 : F) * a0 * a4 * a5 ^ 4 * h ^ 36
    + (155889360 : F) * a0 * a5 ^ 4 * b8 * h ^ 32
    + (259815600 : F) * a1 * a3 * a5 ^ 4 * h ^ 36
    + (272806380 : F) * a1 * a4 * a5 ^ 4 * h ^ 35 * lambda
    + (136403190 : F) * a1 * a5 ^ 4 * b7 * h ^ 32
    + (129907800 : F) * a2 ^ 2 * a5 ^ 4 * h ^ 36
    + (272806380 : F) * a2 * a3 * a5 ^ 4 * h ^ 35 * lambda
    - (151559100 : F) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 30
    - (727483680 : F) * a2 * a4 * a5 ^ 4 * b8 * h ^ 26
    + (116917020 : F) * a2 * a5 ^ 4 * b6 * h ^ 32
    - (151559100 : F) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 30
    - (363741840 : F) * a3 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (772951410 : F) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 29 * lambda
    - (636548220 : F) * a3 * a4 * a5 ^ 4 * b7 * h ^ 26
    + (97430850 : F) * a3 * a5 ^ 4 * b5 * h ^ 32
    - (143139150 : F) * a4 ^ 4 * a5 ^ 4 * h ^ 24
    + (687067920 : F) * a4 ^ 3 * a5 ^ 4 * b8 * h ^ 20
    - (272806380 : F) * a4 ^ 2 * a5 ^ 4 * b6 * h ^ 26
    + (77944680 : F) * a4 * a5 ^ 4 * b4 * h ^ 32
    - (10628820 : F) * a5 ^ 4 * b2 * h ^ 38
    - (177147000 : F) * a0 * a3 * a5 ^ 3 * h ^ 42
    - (233834040 : F) * a0 * a4 * a5 ^ 3 * h ^ 41 * lambda
    - (148803480 : F) * a0 * a5 ^ 3 * b7 * h ^ 38
    - (177147000 : F) * a1 * a2 * a5 ^ 3 * h ^ 42
    - (233834040 : F) * a1 * a3 * a5 ^ 3 * h ^ 41 * lambda
    - (64953900 : F) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    + (623557440 : F) * a1 * a4 * a5 ^ 3 * b8 * h ^ 32
    - (127545840 : F) * a1 * a5 ^ 3 * b6 * h ^ 38
    - (116917020 : F) * a2 ^ 2 * a5 ^ 3 * h ^ 41 * lambda
    - (129907800 : F) * a2 * a3 * a4 * a5 ^ 3 * h ^ 36
    + (623557440 : F) * a2 * a3 * a5 ^ 3 * b8 * h ^ 32
    + (545612760 : F) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 35 * lambda
    + (545612760 : F) * a2 * a4 * a5 ^ 3 * b7 * h ^ 32
    - (106288200 : F) * a2 * a5 ^ 3 * b5 * h ^ 38
    - (21651300 : F) * a3 ^ 3 * a5 ^ 3 * h ^ 36
    + (545612760 : F) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 35 * lambda
    + (272806380 : F) * a3 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (707275800 : F) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 30
    - (1454967360 : F) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    + (467668080 : F) * a3 * a4 * a5 ^ 3 * b6 * h ^ 32
    - (85030560 : F) * a3 * a5 ^ 3 * b4 * h ^ 38
    - (257650470 : F) * a4 ^ 4 * a5 ^ 3 * h ^ 29 * lambda
    - (424365480 : F) * a4 ^ 3 * a5 ^ 3 * b7 * h ^ 26
    + (194861700 : F) * a4 ^ 2 * a5 ^ 3 * b5 * h ^ 32
    - (63772920 : F) * a4 * a5 ^ 3 * b3 * h ^ 38
    + (7971615 : F) * a5 ^ 3 * b1 * h ^ 44
    + (79716150 : F) * a0 * a2 * a5 ^ 2 * h ^ 48
    + (191318760 : F) * a0 * a3 * a5 ^ 2 * h ^ 47 * lambda
    + (212576400 : F) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    - (510183360 : F) * a0 * a4 * a5 ^ 2 * b8 * h ^ 38
    + (143489070 : F) * a0 * a5 ^ 2 * b6 * h ^ 44
    + (39858075 : F) * a1 ^ 2 * a5 ^ 2 * h ^ 48
    + (191318760 : F) * a1 * a2 * a5 ^ 2 * h ^ 47 * lambda
    + (425152800 : F) * a1 * a3 * a4 * a5 ^ 2 * h ^ 42
    - (510183360 : F) * a1 * a3 * a5 ^ 2 * b8 * h ^ 38
    - (350751060 : F) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    - (446410440 : F) * a1 * a4 * a5 ^ 2 * b7 * h ^ 38
    + (119574225 : F) * a1 * a5 ^ 2 * b5 * h ^ 44
    + (212576400 : F) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 42
    - (255091680 : F) * a2 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    + (212576400 : F) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 42
    - (701502120 : F) * a2 * a3 * a4 * a5 ^ 2 * h ^ 41 * lambda
    - (446410440 : F) * a2 * a3 * a5 ^ 2 * b7 * h ^ 38
    - (649539000 : F) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 36
    + (935336160 : F) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 32
    - (382637520 : F) * a2 * a4 * a5 ^ 2 * b6 * h ^ 38
    + (95659380 : F) * a2 * a5 ^ 2 * b4 * h ^ 44
    - (116917020 : F) * a3 ^ 3 * a5 ^ 2 * h ^ 41 * lambda
    - (974308500 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    + (935336160 : F) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * h ^ 32
    - (191318760 : F) * a3 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    + (545612760 : F) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 35 * lambda
    + (818419140 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (318864600 : F) * a3 * a4 * a5 ^ 2 * b5 * h ^ 38
    + (71744535 : F) * a3 * a5 ^ 2 * b3 * h ^ 44
    + (242494560 : F) * a4 ^ 5 * a5 ^ 2 * h ^ 30
    - (363741840 : F) * a4 ^ 4 * a5 ^ 2 * b8 * h ^ 26
    + (233834040 : F) * a4 ^ 3 * a5 ^ 2 * b6 * h ^ 32
    - (127545840 : F) * a4 ^ 2 * a5 ^ 2 * b4 * h ^ 38
    + (47829690 : F) * a4 * a5 ^ 2 * b2 * h ^ 44
    + (47829690 : F) * a0 * a1 * a5 * h ^ 54
    - (143489070 : F) * a0 * a2 * a5 * h ^ 53 * lambda
    - (558013050 : F) * a0 * a3 * a4 * a5 * h ^ 48
    + (382637520 : F) * a0 * a3 * a5 * b8 * h ^ 44
    + (191318760 : F) * a0 * a4 ^ 2 * a5 * h ^ 47 * lambda
    + (334807830 : F) * a0 * a4 * a5 * b7 * h ^ 44
    - (143489070 : F) * a0 * a5 * b5 * h ^ 50
    - (71744535 : F) * a1 ^ 2 * a5 * h ^ 53 * lambda
    - (558013050 : F) * a1 * a2 * a4 * a5 * h ^ 48
    + (382637520 : F) * a1 * a2 * a5 * b8 * h ^ 44
    - (279006525 : F) * a1 * a3 ^ 2 * a5 * h ^ 48
    + (382637520 : F) * a1 * a3 * a4 * a5 * h ^ 47 * lambda
    + (334807830 : F) * a1 * a3 * a5 * b7 * h ^ 44
    + (460582200 : F) * a1 * a4 ^ 3 * a5 * h ^ 42
    - (510183360 : F) * a1 * a4 ^ 2 * a5 * b8 * h ^ 38
    + (286978140 : F) * a1 * a4 * a5 * b6 * h ^ 44
    - (114791256 : F) * a1 * a5 * b4 * h ^ 50
    - (279006525 : F) * a2 ^ 2 * a3 * a5 * h ^ 48
    + (191318760 : F) * a2 ^ 2 * a4 * a5 * h ^ 47 * lambda
    + (167403915 : F) * a2 ^ 2 * a5 * b7 * h ^ 44
    + (191318760 : F) * a2 * a3 ^ 2 * a5 * h ^ 47 * lambda
    + (1381746600 : F) * a2 * a3 * a4 ^ 2 * a5 * h ^ 42
    - (1020366720 : F) * a2 * a3 * a4 * a5 * b8 * h ^ 38
    + (286978140 : F) * a2 * a3 * a5 * b6 * h ^ 44
    - (233834040 : F) * a2 * a4 ^ 3 * a5 * h ^ 41 * lambda
    - (446410440 : F) * a2 * a4 ^ 2 * a5 * b7 * h ^ 38
    + (239148450 : F) * a2 * a4 * a5 * b5 * h ^ 44
    - (86093442 : F) * a2 * a5 * b3 * h ^ 50
    + (460582200 : F) * a3 ^ 3 * a4 * a5 * h ^ 42
    - (170061120 : F) * a3 ^ 3 * a5 * b8 * h ^ 38
    - (350751060 : F) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 41 * lambda
    - (446410440 : F) * a3 ^ 2 * a4 * a5 * b7 * h ^ 38
    + (119574225 : F) * a3 ^ 2 * a5 * b5 * h ^ 44
    - (617062050 : F) * a3 * a4 ^ 4 * a5 * h ^ 36
    + (623557440 : F) * a3 * a4 ^ 3 * a5 * b8 * h ^ 32
    - (382637520 : F) * a3 * a4 ^ 2 * a5 * b6 * h ^ 38
    + (191318760 : F) * a3 * a4 * a5 * b4 * h ^ 44
    - (57395628 : F) * a3 * a5 * b2 * h ^ 50
    + (54561276 : F) * a4 ^ 5 * a5 * h ^ 35 * lambda
    + (136403190 : F) * a4 ^ 4 * a5 * b7 * h ^ 32
    - (106288200 : F) * a4 ^ 3 * a5 * b5 * h ^ 38
    + (71744535 : F) * a4 ^ 2 * a5 * b3 * h ^ 44
    - (28697814 : F) * a4 * a5 * b1 * h ^ 50
    - (143489070 : F) * a0 ^ 2 * h ^ 60
    + (86093442 : F) * a0 * a1 * h ^ 59 * lambda
    + (478296900 : F) * a0 * a2 * a4 * h ^ 54
    - (229582512 : F) * a0 * a2 * b8 * h ^ 50
    + (239148450 : F) * a0 * a3 ^ 2 * h ^ 54
    - (143489070 : F) * a0 * a3 * a4 * h ^ 53 * lambda
    - (200884698 : F) * a0 * a3 * b7 * h ^ 50
    - (212576400 : F) * a0 * a4 ^ 3 * h ^ 48
    + (191318760 : F) * a0 * a4 ^ 2 * b8 * h ^ 44
    - (172186884 : F) * a0 * a4 * b6 * h ^ 50
    + (172186884 : F) * a0 * b4 * h ^ 56
    + (239148450 : F) * a1 ^ 2 * a4 * h ^ 54
    - (114791256 : F) * a1 ^ 2 * b8 * h ^ 50
    + (478296900 : F) * a1 * a2 * a3 * h ^ 54
    - (143489070 : F) * a1 * a2 * a4 * h ^ 53 * lambda
    - (200884698 : F) * a1 * a2 * b7 * h ^ 50
    - (71744535 : F) * a1 * a3 ^ 2 * h ^ 53 * lambda
    - (637729200 : F) * a1 * a3 * a4 ^ 2 * h ^ 48
    + (382637520 : F) * a1 * a3 * a4 * b8 * h ^ 44
    - (172186884 : F) * a1 * a3 * b6 * h ^ 50
    + (63772920 : F) * a1 * a4 ^ 3 * h ^ 47 * lambda
    + (167403915 : F) * a1 * a4 ^ 2 * b7 * h ^ 44
    - (143489070 : F) * a1 * a4 * b5 * h ^ 50
    + (129140163 : F) * a1 * b3 * h ^ 56
    + (79716150 : F) * a2 ^ 3 * h ^ 54
    - (71744535 : F) * a2 ^ 2 * a3 * h ^ 53 * lambda
    - (318864600 : F) * a2 ^ 2 * a4 ^ 2 * h ^ 48
    + (191318760 : F) * a2 ^ 2 * a4 * b8 * h ^ 44
    - (86093442 : F) * a2 ^ 2 * b6 * h ^ 50
    - (637729200 : F) * a2 * a3 ^ 2 * a4 * h ^ 48
    + (191318760 : F) * a2 * a3 ^ 2 * b8 * h ^ 44
    + (191318760 : F) * a2 * a3 * a4 ^ 2 * h ^ 47 * lambda
    + (334807830 : F) * a2 * a3 * a4 * b7 * h ^ 44
    - (143489070 : F) * a2 * a3 * b5 * h ^ 50
    + (194861700 : F) * a2 * a4 ^ 4 * h ^ 42
    - (170061120 : F) * a2 * a4 ^ 3 * b8 * h ^ 38
    + (143489070 : F) * a2 * a4 ^ 2 * b6 * h ^ 44
    - (114791256 : F) * a2 * a4 * b4 * h ^ 50
    + (86093442 : F) * a2 * b2 * h ^ 56
    - (53144100 : F) * a3 ^ 4 * h ^ 48
    + (63772920 : F) * a3 ^ 3 * a4 * h ^ 47 * lambda
    + (55801305 : F) * a3 ^ 3 * b7 * h ^ 44
    + (389723400 : F) * a3 ^ 2 * a4 ^ 3 * h ^ 42
    - (255091680 : F) * a3 ^ 2 * a4 ^ 2 * b8 * h ^ 38
    + (143489070 : F) * a3 ^ 2 * a4 * b6 * h ^ 44
    - (57395628 : F) * a3 ^ 2 * b4 * h ^ 50
    - (58458510 : F) * a3 * a4 ^ 4 * h ^ 41 * lambda
    - (148803480 : F) * a3 * a4 ^ 3 * b7 * h ^ 38
    + (119574225 : F) * a3 * a4 ^ 2 * b5 * h ^ 44
    - (86093442 : F) * a3 * a4 * b3 * h ^ 50
    + (43046721 : F) * a3 * b1 * h ^ 56
    - (30311820 : F) * a4 ^ 6 * h ^ 36
    + (31177872 : F) * a4 ^ 5 * b8 * h ^ 32
    - (31886460 : F) * a4 ^ 4 * b6 * h ^ 38
    + (31886460 : F) * a4 ^ 3 * b4 * h ^ 44
    - (28697814 : F) * a4 ^ 2 * b2 * h ^ 50 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h5 : (5 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h36 : (36 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h1296 : (1296 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h31104 : (31104 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have h6561 : (6561 : F) ≠ 0 := by norm_num
  have h258280326 : (258280326 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hh55 : h ^ 55 ≠ 0 := pow_ne_zero 55 hh
  have hh60 : h ^ 60 ≠ 0 := pow_ne_zero 60 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hC :
      depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
            24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
          (144 * h ^ 20) :=
    depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD0 :
      depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
            27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
            a5 ^ 5) /
          (324 * h ^ 25) :=
    depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE0 :
      depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
        (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
            1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
            36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
          (46656 * h ^ 30) :=
    depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hT :
      depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU :
      depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV :
      depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 =
        (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
            112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
            2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
            31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
            186624 * b2 * h ^ 38) /
          (186624 * h ^ 40) :=
    depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hW :
      terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) :=
    terminalDepressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  simp only [bridgeLambdaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hW, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h32,
    h36, h54, h64, h72, h81, h144, h216, h243, h256, h324, h432, h648,
    h729, h1296, h6561, h7776, h11664, h31104, h46656, h93312, h186624,
    h5038848, h258280326, hh10, hh15, hh20, hh25, hh30, hh35, hh40, hh45,
    hh50, hh55, hh60]
  ring

end BridgeLambdaDepression610

/-! ## Degree-`3` depressed differential row -/

section BridgeLambdaDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic, the degree-`3`
Jacobian coefficient is exactly `4 T E' + 3 U D' + 2 V C' + W B'
- D U' - 2 C V' - 3 B W' - 4 A X'`. -/
theorem differentialJacobian_coeff_3_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 6 < n → f.coeff n = 0) (_hf6 : f.coeff 6 = 1)
    (_hf5 : f.coeff 5 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        (1 : F) * g.coeff 1 * d (f.coeff 3) -
          (1 : F) * f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne03_12 : ((0, 3) : ℕ × ℕ) ≠ (1, 2) := by decide
  have hne03_21 : ((0, 3) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne03_30 : ((0, 3) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne12_21 : ((1, 2) : ℕ × ℕ) ≠ (2, 1) := by decide
  have hne12_30 : ((1, 2) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hne21_30 : ((2, 1) : ℕ × ℕ) ≠ (3, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 3 =
        (4 : F) * g.coeff 4 * d (f.coeff 0) +
          (3 : F) * g.coeff 3 * d (f.coeff 1) +
          (2 : F) * g.coeff 2 * d (f.coeff 2) +
          (1 : F) * g.coeff 1 * d (f.coeff 3) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]), Finset.sum_singleton]
      ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder3g, hder2g,
      hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 3 =
        (1 : F) * f.coeff 1 * d (g.coeff 3) +
          (2 : F) * f.coeff 2 * d (g.coeff 2) +
          (3 : F) * f.coeff 3 * d (g.coeff 1) +
          (4 : F) * f.coeff 4 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne03_12, hne03_21, hne03_30]),
        Finset.sum_insert (by simp [hne12_21, hne12_30]),
        Finset.sum_insert (by simp [hne21_30]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder0, hder1,
      hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 80000000 in
theorem bridgeLambdaResidual610_deriv_zero
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
    (hrow : (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + (1 : F) * W0 * d B -
        (1 : F) * D0 * d U0 - (2 : F) * C0 * d V0 -
        (3 : F) * B * d W0 - (4 : F) * A * d X0 = 0) :
    d (bridgeLambdaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
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
  have hrow_red := hrow
  simp only [hXderiv, hWderiv, hPderiv, hQderiv, hRderiv, hSderiv,
    hTderiv, hUderiv, hVderiv] at hrow_red
  simp only [bridgeLambdaResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h16f, h13, h12, hx14, hx19, h23, h29, h34, h38, h316,
    h332, h49, h427, h481, hx59, h527, h536, h581, hx5243, h736, h827,
    hx8729, hx932, h1027, hx1081, hx15256, h2081, h20243, hx35216,
    h35432, h35729, h351296, hx356561, hx70729, hx3857776, hL, halpha,
    hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta, hsq, hsqB,
    hsqC, hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint, hsext,
    pow_two, pow_three, zero_mul, add_zero, mul_zero]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610, pow_two, pow_three]
  linear_combination (1 / 6 : F) * hrow_red

end BridgeLambdaDepressedRow610

/-! ## Weight-`60` power relation on the literal source -/

section BridgeLambdaPowerRelation610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The eleventh sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁶⁰`.  The weight-fifty `ι` and
weight-fifty-five `κ` residuals remain available from the terminal and
kappa bridge packets. -/
theorem nonzeroFace610_bridgeLambdaPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ nu : k,
      bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C nu * h0 ^ 60 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        terminalDepressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610_bridge (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [terminalDepressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow3 :
      (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 0) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 1) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 2) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 3) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 3) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 2) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 1) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_3_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 3) hbracket
    simpa [f, g, Polynomial.coeff_C, show (3 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow12)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  have heps0deriv :
      ratFuncDerivation68
        (epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow9)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 (by simpa using hrow8)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2) hLconst halpha0 hbeta0 hgamma0 hdelta0 heps0deriv
      (by simpa using hrow7)
  have htheta0deriv :
      ratFuncDerivation68
        (bridgeThetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1)) = 0 :=
    bridgeThetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1) hLconst halpha0 hbeta0 hgamma0 hdelta0
      heps0deriv hzeta0deriv (by simpa using hrow6)
  have hlambda0deriv :
      ratFuncDerivation68
        (bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    bridgeLambdaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha0
      hbeta0 hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      htheta0deriv (by simpa using hrow6) (by simpa using hrow5)
      (by simpa using hrow3)
  obtain ⟨nu0, hnu0⟩ :
      ∃ a : k,
        bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hlambda0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (258280326 : RatFunc k) * hRF ^ 60 *
          bridgeLambdaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := bridgeLambdaDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [bridgeClearedLambdaDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, b1, bridgeLambdaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, zetaResidual610, etaResidual610,
      bridgeThetaResidual610, hf4, hf3, hf2, hf1, hf0, hg1, hg2, hg3, hg4, hg5,
      hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (258280326 * nu0) * h0 ^ 60) := by
    rw [hclear, hnu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨258280326 * nu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end BridgeLambdaPowerRelation610

/-! ## Jet heads and tails of the cleared `λ` defect -/

section BridgeLambdaJet610

variable {R : Type*} [CommRing R]

/-- Order-`52` head of the jet-substituted cleared `λ` defect: the
coefficient of `h⁵²` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `bridgeClearedLambdaDefect610`,
kept in its fully factored form. -/
def bridgeLambdaJetHead610 (p31 u1 q4 : R) : R :=
  (531441 : R) * p31 ^ 2 *
    ((105 : R) * p31 * u1 - (100 : R) * p31 ^ 2 - (108 : R) * q4)

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `λ` defect above order `h⁵³`. -/
def bridgeLambdaJetTail610
    (hh w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 lam : R) : R :=
    (460582200 : R) * w1 * a41 * p31 ^ 3
    - (446410440 : R) * w1 * a41 * p31 ^ 2 * u1
    + (191318760 : R) * w1 * a41 * p31 * q4
    - (170061120 : R) * w1 * p31 ^ 3 * s1
    + (119574225 : R) * w1 * p31 ^ 2 * q52
    + (389723400 : R) * a41 ^ 3 * p31 ^ 2
    - (148803480 : R) * a41 ^ 3 * p31 * u1
    + (31886460 : R) * a41 ^ 3 * q4
    - (255091680 : R) * a41 ^ 2 * p31 ^ 2 * s1
    + (119574225 : R) * a41 ^ 2 * p31 * q52
    + (143489070 : R) * a41 * p31 ^ 2 * b62
    - (637729200 : R) * a41 * p31 ^ 2 * p2
    + (334807830 : R) * a41 * p31 * u1 * p2
    - (114791256 : R) * a41 * p2 * q4
    + (191318760 : R) * p31 ^ 2 * s1 * p2
    - (143489070 : R) * p31 * q52 * p2
    + (63772920 : R) * lam * a41 * p31 ^ 3
    - (21651300 : R) * hh * w1 ^ 3 * p31 ^ 3
    + (272806380 : R) * hh * w1 ^ 3 * p31 ^ 2 * u1
    - (85030560 : R) * hh * w1 ^ 3 * p31 * q4
    - (974308500 : R) * hh * w1 ^ 2 * a41 ^ 2 * p31 ^ 2
    + (818419140 : R) * hh * w1 ^ 2 * a41 ^ 2 * p31 * u1
    - (127545840 : R) * hh * w1 ^ 2 * a41 ^ 2 * q4
    + (935336160 : R) * hh * w1 ^ 2 * a41 * p31 ^ 2 * s1
    - (318864600 : R) * hh * w1 ^ 2 * a41 * p31 * q52
    - (191318760 : R) * hh * w1 ^ 2 * p31 ^ 2 * b62
    + (212576400 : R) * hh * w1 ^ 2 * p31 ^ 2 * p2
    - (446410440 : R) * hh * w1 ^ 2 * p31 * u1 * p2
    + (95659380 : R) * hh * w1 ^ 2 * p2 * q4
    - (617062050 : R) * hh * w1 * a41 ^ 4 * p31
    + (136403190 : R) * hh * w1 * a41 ^ 4 * u1
    + (623557440 : R) * hh * w1 * a41 ^ 3 * p31 * s1
    - (106288200 : R) * hh * w1 * a41 ^ 3 * q52
    - (382637520 : R) * hh * w1 * a41 ^ 2 * p31 * b62
    + (1381746600 : R) * hh * w1 * a41 ^ 2 * p31 * p2
    - (446410440 : R) * hh * w1 * a41 ^ 2 * u1 * p2
    - (1020366720 : R) * hh * w1 * a41 * p31 * s1 * p2
    + (239148450 : R) * hh * w1 * a41 * q52 * p2
    + (286978140 : R) * hh * w1 * p31 * b62 * p2
    - (279006525 : R) * hh * w1 * p31 * p2 ^ 2
    + (167403915 : R) * hh * w1 * u1 * p2 ^ 2
    - (30311820 : R) * hh * a41 ^ 6
    + (31177872 : R) * hh * a41 ^ 5 * s1
    - (31886460 : R) * hh * a41 ^ 4 * b62
    + (194861700 : R) * hh * a41 ^ 4 * p2
    - (170061120 : R) * hh * a41 ^ 3 * s1 * p2
    + (143489070 : R) * hh * a41 ^ 2 * b62 * p2
    - (318864600 : R) * hh * a41 ^ 2 * p2 ^ 2
    - (86093442 : R) * hh * a41 * p31 * q3
    + (191318760 : R) * hh * a41 * s1 * p2 ^ 2
    - (86093442 : R) * hh * b62 * p2 ^ 2
    + (79716150 : R) * hh * p2 ^ 3
    - (116917020 : R) * hh * lam * w1 ^ 2 * p31 ^ 3
    - (350751060 : R) * hh * lam * w1 * a41 ^ 2 * p31 ^ 2
    + (191318760 : R) * hh * lam * w1 * p31 ^ 2 * p2
    - (58458510 : R) * hh * lam * a41 ^ 4 * p31
    + (191318760 : R) * hh * lam * a41 ^ 2 * p31 * p2
    - (71744535 : R) * hh * lam * p31 * p2 ^ 2
    - (151559100 : R) * hh ^ 2 * w1 ^ 4 * a41 * p31 ^ 2
    - (636548220 : R) * hh ^ 2 * w1 ^ 4 * a41 * p31 * u1
    + (77944680 : R) * hh ^ 2 * w1 ^ 4 * a41 * q4
    - (363741840 : R) * hh ^ 2 * w1 ^ 4 * p31 ^ 2 * s1
    + (97430850 : R) * hh ^ 2 * w1 ^ 4 * p31 * q52
    + (707275800 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 3 * p31
    - (424365480 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 3 * u1
    - (1454967360 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p31 * s1
    + (194861700 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * q52
    + (467668080 : R) * hh ^ 2 * w1 ^ 3 * a41 * p31 * b62
    - (129907800 : R) * hh ^ 2 * w1 ^ 3 * a41 * p31 * p2
    + (545612760 : R) * hh ^ 2 * w1 ^ 3 * a41 * u1 * p2
    + (623557440 : R) * hh ^ 2 * w1 ^ 3 * p31 * s1 * p2
    - (106288200 : R) * hh ^ 2 * w1 ^ 3 * q52 * p2
    + (242494560 : R) * hh ^ 2 * w1 ^ 2 * a41 ^ 5
    - (363741840 : R) * hh ^ 2 * w1 ^ 2 * a41 ^ 4 * s1
    + (233834040 : R) * hh ^ 2 * w1 ^ 2 * a41 ^ 3 * b62
    - (649539000 : R) * hh ^ 2 * w1 ^ 2 * a41 ^ 3 * p2
    + (935336160 : R) * hh ^ 2 * w1 ^ 2 * a41 ^ 2 * s1 * p2
    - (382637520 : R) * hh ^ 2 * w1 ^ 2 * a41 * b62 * p2
    + (212576400 : R) * hh ^ 2 * w1 ^ 2 * a41 * p2 ^ 2
    + (71744535 : R) * hh ^ 2 * w1 ^ 2 * p31 * q3
    - (255091680 : R) * hh ^ 2 * w1 ^ 2 * s1 * p2 ^ 2
    + (71744535 : R) * hh ^ 2 * w1 * a41 ^ 2 * q3
    - (279006525 : R) * hh ^ 2 * w1 * p31 ^ 2 * p1
    + (334807830 : R) * hh ^ 2 * w1 * p31 * u1 * p1
    - (86093442 : R) * hh ^ 2 * w1 * p2 * q3
    - (114791256 : R) * hh ^ 2 * w1 * p1 * q4
    - (637729200 : R) * hh ^ 2 * a41 ^ 2 * p31 * p1
    + (167403915 : R) * hh ^ 2 * a41 ^ 2 * u1 * p1
    + (382637520 : R) * hh ^ 2 * a41 * p31 * s1 * p1
    - (143489070 : R) * hh ^ 2 * a41 * q52 * p1
    - (172186884 : R) * hh ^ 2 * p31 * b62 * p1
    + (478296900 : R) * hh ^ 2 * p31 * p2 * p1
    - (200884698 : R) * hh ^ 2 * u1 * p2 * p1
    + (545612760 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 * p31 ^ 2
    + (545612760 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 3 * p31
    - (701502120 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 * p31 * p2
    + (54561276 : R) * hh ^ 2 * lam * w1 * a41 ^ 5
    - (233834040 : R) * hh ^ 2 * lam * w1 * a41 ^ 3 * p2
    + (191318760 : R) * hh ^ 2 * lam * w1 * a41 * p2 ^ 2
    - (71744535 : R) * hh ^ 2 * lam * p31 ^ 2 * p1
    + (200394810 : R) * hh ^ 3 * w1 ^ 6 * p31 ^ 2
    + (120236886 : R) * hh ^ 3 * w1 ^ 6 * p31 * u1
    - (12124728 : R) * hh ^ 3 * w1 ^ 6 * q4
    + (429417450 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 2 * p31
    + (360710658 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 2 * u1
    + (824481504 : R) * hh ^ 3 * w1 ^ 5 * a41 * p31 * s1
    - (90935460 : R) * hh ^ 3 * w1 ^ 5 * a41 * q52
    - (109122552 : R) * hh ^ 3 * w1 ^ 5 * p31 * b62
    - (333430020 : R) * hh ^ 3 * w1 ^ 5 * p31 * p2
    - (127309644 : R) * hh ^ 3 * w1 ^ 5 * u1 * p2
    - (143139150 : R) * hh ^ 3 * w1 ^ 4 * a41 ^ 4
    + (687067920 : R) * hh ^ 3 * w1 ^ 4 * a41 ^ 3 * s1
    - (272806380 : R) * hh ^ 3 * w1 ^ 4 * a41 ^ 2 * b62
    - (151559100 : R) * hh ^ 3 * w1 ^ 4 * a41 ^ 2 * p2
    - (727483680 : R) * hh ^ 3 * w1 ^ 4 * a41 * s1 * p2
    + (116917020 : R) * hh ^ 3 * w1 ^ 4 * b62 * p2
    + (129907800 : R) * hh ^ 3 * w1 ^ 4 * p2 ^ 2
    - (63772920 : R) * hh ^ 3 * w1 ^ 3 * a41 * q3
    + (425152800 : R) * hh ^ 3 * w1 ^ 2 * a41 * p31 * p1
    - (446410440 : R) * hh ^ 3 * w1 ^ 2 * a41 * u1 * p1
    - (510183360 : R) * hh ^ 3 * w1 ^ 2 * p31 * s1 * p1
    + (119574225 : R) * hh ^ 3 * w1 ^ 2 * q52 * p1
    + (460582200 : R) * hh ^ 3 * w1 * a41 ^ 3 * p1
    - (510183360 : R) * hh ^ 3 * w1 * a41 ^ 2 * s1 * p1
    + (286978140 : R) * hh ^ 3 * w1 * a41 * b62 * p1
    - (558013050 : R) * hh ^ 3 * w1 * a41 * p2 * p1
    - (57395628 : R) * hh ^ 3 * w1 * p31 * q2
    + (382637520 : R) * hh ^ 3 * w1 * s1 * p2 * p1
    - (28697814 : R) * hh ^ 3 * a41 ^ 2 * q2
    + (239148450 : R) * hh ^ 3 * p31 ^ 2 * p0
    - (200884698 : R) * hh ^ 3 * p31 * u1 * p0
    + (86093442 : R) * hh ^ 3 * p2 * q2
    + (129140163 : R) * hh ^ 3 * p1 * q3
    + (172186884 : R) * hh ^ 3 * p0 * q4
    - (154590282 : R) * hh ^ 3 * lam * w1 ^ 5 * p31 ^ 2
    - (772951410 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 ^ 2 * p31
    + (272806380 : R) * hh ^ 3 * lam * w1 ^ 4 * p31 * p2
    - (257650470 : R) * hh ^ 3 * lam * w1 ^ 3 * a41 ^ 4
    + (545612760 : R) * hh ^ 3 * lam * w1 ^ 3 * a41 ^ 2 * p2
    - (116917020 : R) * hh ^ 3 * lam * w1 ^ 3 * p2 ^ 2
    + (382637520 : R) * hh ^ 3 * lam * w1 * a41 * p31 * p1
    + (63772920 : R) * hh ^ 3 * lam * a41 ^ 3 * p1
    - (143489070 : R) * hh ^ 3 * lam * a41 * p2 * p1
    - (463498200 : R) * hh ^ 4 * w1 ^ 7 * a41 * p31
    - (114511320 : R) * hh ^ 4 * w1 ^ 7 * a41 * u1
    - (130870080 : R) * hh ^ 4 * w1 ^ 7 * p31 * s1
    + (12269070 : R) * hh ^ 4 * w1 ^ 7 * q52
    - (254469600 : R) * hh ^ 4 * w1 ^ 6 * a41 ^ 3
    - (458045280 : R) * hh ^ 4 * w1 ^ 6 * a41 ^ 2 * s1
    + (103060188 : R) * hh ^ 4 * w1 ^ 6 * a41 * b62
    + (400789620 : R) * hh ^ 4 * w1 ^ 6 * a41 * p2
    + (137413584 : R) * hh ^ 4 * w1 ^ 6 * s1 * p2
    + (11691702 : R) * hh ^ 4 * w1 ^ 5 * q3
    + (259815600 : R) * hh ^ 4 * w1 ^ 4 * p31 * p1
    + (136403190 : R) * hh ^ 4 * w1 ^ 4 * u1 * p1
    - (64953900 : R) * hh ^ 4 * w1 ^ 3 * a41 ^ 2 * p1
    + (623557440 : R) * hh ^ 4 * w1 ^ 3 * a41 * s1 * p1
    - (127545840 : R) * hh ^ 4 * w1 ^ 3 * b62 * p1
    - (177147000 : R) * hh ^ 4 * w1 ^ 3 * p2 * p1
    + (47829690 : R) * hh ^ 4 * w1 ^ 2 * a41 * q2
    - (558013050 : R) * hh ^ 4 * w1 * a41 * p31 * p0
    + (334807830 : R) * hh ^ 4 * w1 * a41 * u1 * p0
    + (382637520 : R) * hh ^ 4 * w1 * p31 * s1 * p0
    - (143489070 : R) * hh ^ 4 * w1 * q52 * p0
    - (212576400 : R) * hh ^ 4 * a41 ^ 3 * p0
    + (191318760 : R) * hh ^ 4 * a41 ^ 2 * s1 * p0
    - (172186884 : R) * hh ^ 4 * a41 * b62 * p0
    + (478296900 : R) * hh ^ 4 * a41 * p2 * p0
    + (239148450 : R) * hh ^ 4 * a41 * p1 ^ 2
    + (43046721 : R) * hh ^ 4 * p31 * q1
    - (229582512 : R) * hh ^ 4 * s1 * p2 * p0
    - (114791256 : R) * hh ^ 4 * s1 * p1 ^ 2
    + (343533960 : R) * hh ^ 4 * lam * w1 ^ 6 * a41 * p31
    + (343533960 : R) * hh ^ 4 * lam * w1 ^ 5 * a41 ^ 3
    - (309180564 : R) * hh ^ 4 * lam * w1 ^ 5 * a41 * p2
    - (233834040 : R) * hh ^ 4 * lam * w1 ^ 3 * p31 * p1
    - (350751060 : R) * hh ^ 4 * lam * w1 ^ 2 * a41 ^ 2 * p1
    + (191318760 : R) * hh ^ 4 * lam * w1 ^ 2 * p2 * p1
    - (143489070 : R) * hh ^ 4 * lam * a41 * p31 * p0
    + (84192075 : R) * hh ^ 5 * w1 ^ 9 * p31
    + (12193335 : R) * hh ^ 5 * w1 ^ 9 * u1
    + (261285750 : R) * hh ^ 5 * w1 ^ 8 * a41 ^ 2
    + (125417160 : R) * hh ^ 5 * w1 ^ 8 * a41 * s1
    - (12269070 : R) * hh ^ 5 * w1 ^ 8 * b62
    - (88609950 : R) * hh ^ 5 * w1 ^ 8 * p2
    - (333430020 : R) * hh ^ 5 * w1 ^ 5 * a41 * p1
    - (145496736 : R) * hh ^ 5 * w1 ^ 5 * s1 * p1
    - (10628820 : R) * hh ^ 5 * w1 ^ 4 * q2
    - (177147000 : R) * hh ^ 5 * w1 ^ 3 * p31 * p0
    - (148803480 : R) * hh ^ 5 * w1 ^ 3 * u1 * p0
    + (212576400 : R) * hh ^ 5 * w1 ^ 2 * a41 ^ 2 * p0
    - (510183360 : R) * hh ^ 5 * w1 ^ 2 * a41 * s1 * p0
    + (143489070 : R) * hh ^ 5 * w1 ^ 2 * b62 * p0
    + (79716150 : R) * hh ^ 5 * w1 ^ 2 * p2 * p0
    + (39858075 : R) * hh ^ 5 * w1 ^ 2 * p1 ^ 2
    - (28697814 : R) * hh ^ 5 * w1 * a41 * q1
    - (47031435 : R) * hh ^ 5 * lam * w1 ^ 8 * p31
    - (188125740 : R) * hh ^ 5 * lam * w1 ^ 7 * a41 ^ 2
    + (49076280 : R) * hh ^ 5 * lam * w1 ^ 7 * p2
    + (272806380 : R) * hh ^ 5 * lam * w1 ^ 4 * a41 * p1
    + (191318760 : R) * hh ^ 5 * lam * w1 ^ 2 * p31 * p0
    + (191318760 : R) * hh ^ 5 * lam * w1 * a41 ^ 2 * p0
    - (143489070 : R) * hh ^ 5 * lam * w1 * p2 * p0
    - (71744535 : R) * hh ^ 5 * lam * w1 * p1 ^ 2
    - (80514720 : R) * hh ^ 6 * w1 ^ 10 * a41
    - (12077208 : R) * hh ^ 6 * w1 ^ 10 * s1
    + (94062870 : R) * hh ^ 6 * w1 ^ 7 * p1
    + (259815600 : R) * hh ^ 6 * w1 ^ 4 * a41 * p0
    + (155889360 : R) * hh ^ 6 * w1 ^ 4 * s1 * p0
    + (7971615 : R) * hh ^ 6 * w1 ^ 3 * q1
    + (47829690 : R) * hh ^ 6 * w1 * p1 * p0
    + (45289530 : R) * hh ^ 6 * lam * w1 ^ 9 * a41
    - (51530094 : R) * hh ^ 6 * lam * w1 ^ 6 * p1
    - (233834040 : R) * hh ^ 6 * lam * w1 ^ 3 * a41 * p0
    + (86093442 : R) * hh ^ 6 * lam * p1 * p0
    + (8107385 : R) * hh ^ 7 * w1 ^ 12
    - (101039400 : R) * hh ^ 7 * w1 ^ 6 * p0
    - (143489070 : R) * hh ^ 7 * p0 ^ 2
    - (3979989 : R) * hh ^ 7 * lam * w1 ^ 11
    + (54561276 : R) * hh ^ 7 * lam * w1 ^ 5 * p0

/-- Order-`54` head of the merged-jet cleared `λ` defect: the
coefficient of `h⁵⁴` after the globally merged deeper jet
`p₃ = h² p₃₂`, `q₇ = h⁶ u₂`, `q₅ = h³ q₅₃`, `q₄ = h q₄₁` is
substituted into `bridgeClearedLambdaDefect610`, kept factored through
its content `39366`. -/
def bridgeLambdaDeepHead610 (a41 s1 b62 p2 q41 : R) : R :=
  (39366 : R) *
    ((792 : R) * a41 ^ 5 * s1 - (770 : R) * a41 ^ 6 -
      (810 : R) * a41 ^ 4 * b62 + (4950 : R) * a41 ^ 4 * p2 -
      (4320 : R) * a41 ^ 3 * p2 * s1 + (810 : R) * a41 ^ 3 * q41 +
      (3645 : R) * a41 ^ 2 * b62 * p2 - (8100 : R) * a41 ^ 2 * p2 ^ 2 +
      (4860 : R) * a41 * p2 ^ 2 * s1 - (2916 : R) * a41 * p2 * q41 -
      (2187 : R) * b62 * p2 ^ 2 + (2025 : R) * p2 ^ 3)

set_option maxHeartbeats 40000000 in
/-- Tail of the merged-jet cleared `λ` defect above order `h⁵⁵`. -/
def bridgeLambdaDeepTail610
    (hh w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lam : R) : R :=
    (242494560 : R) * w1 ^ 2 * a41 ^ 5
    - (363741840 : R) * w1 ^ 2 * a41 ^ 4 * s1
    + (233834040 : R) * w1 ^ 2 * a41 ^ 3 * b62
    - (649539000 : R) * w1 ^ 2 * a41 ^ 3 * p2
    + (935336160 : R) * w1 ^ 2 * a41 ^ 2 * s1 * p2
    - (127545840 : R) * w1 ^ 2 * a41 ^ 2 * q41
    - (382637520 : R) * w1 ^ 2 * a41 * b62 * p2
    + (212576400 : R) * w1 ^ 2 * a41 * p2 ^ 2
    - (255091680 : R) * w1 ^ 2 * s1 * p2 ^ 2
    + (95659380 : R) * w1 ^ 2 * p2 * q41
    - (617062050 : R) * w1 * a41 ^ 4 * p32
    + (136403190 : R) * w1 * a41 ^ 4 * u2
    + (623557440 : R) * w1 * a41 ^ 3 * p32 * s1
    - (106288200 : R) * w1 * a41 ^ 3 * q53
    - (382637520 : R) * w1 * a41 ^ 2 * p32 * b62
    + (1381746600 : R) * w1 * a41 ^ 2 * p32 * p2
    - (446410440 : R) * w1 * a41 ^ 2 * u2 * p2
    + (71744535 : R) * w1 * a41 ^ 2 * q3
    - (1020366720 : R) * w1 * a41 * p32 * s1 * p2
    + (191318760 : R) * w1 * a41 * p32 * q41
    + (239148450 : R) * w1 * a41 * q53 * p2
    + (286978140 : R) * w1 * p32 * b62 * p2
    - (279006525 : R) * w1 * p32 * p2 ^ 2
    + (167403915 : R) * w1 * u2 * p2 ^ 2
    - (86093442 : R) * w1 * p2 * q3
    + (389723400 : R) * a41 ^ 3 * p32 ^ 2
    - (148803480 : R) * a41 ^ 3 * p32 * u2
    - (255091680 : R) * a41 ^ 2 * p32 ^ 2 * s1
    + (119574225 : R) * a41 ^ 2 * p32 * q53
    + (143489070 : R) * a41 * p32 ^ 2 * b62
    - (637729200 : R) * a41 * p32 ^ 2 * p2
    + (334807830 : R) * a41 * p32 * u2 * p2
    - (86093442 : R) * a41 * p32 * q3
    + (191318760 : R) * p32 ^ 2 * s1 * p2
    - (57395628 : R) * p32 ^ 2 * q41
    - (143489070 : R) * p32 * q53 * p2
    + (54561276 : R) * lam * w1 * a41 ^ 5
    - (233834040 : R) * lam * w1 * a41 ^ 3 * p2
    + (191318760 : R) * lam * w1 * a41 * p2 ^ 2
    - (58458510 : R) * lam * a41 ^ 4 * p32
    + (191318760 : R) * lam * a41 ^ 2 * p32 * p2
    - (71744535 : R) * lam * p32 * p2 ^ 2
    - (143139150 : R) * hh * w1 ^ 4 * a41 ^ 4
    + (687067920 : R) * hh * w1 ^ 4 * a41 ^ 3 * s1
    - (272806380 : R) * hh * w1 ^ 4 * a41 ^ 2 * b62
    - (151559100 : R) * hh * w1 ^ 4 * a41 ^ 2 * p2
    - (727483680 : R) * hh * w1 ^ 4 * a41 * s1 * p2
    + (77944680 : R) * hh * w1 ^ 4 * a41 * q41
    + (116917020 : R) * hh * w1 ^ 4 * b62 * p2
    + (129907800 : R) * hh * w1 ^ 4 * p2 ^ 2
    + (707275800 : R) * hh * w1 ^ 3 * a41 ^ 3 * p32
    - (424365480 : R) * hh * w1 ^ 3 * a41 ^ 3 * u2
    - (1454967360 : R) * hh * w1 ^ 3 * a41 ^ 2 * p32 * s1
    + (194861700 : R) * hh * w1 ^ 3 * a41 ^ 2 * q53
    + (467668080 : R) * hh * w1 ^ 3 * a41 * p32 * b62
    - (129907800 : R) * hh * w1 ^ 3 * a41 * p32 * p2
    + (545612760 : R) * hh * w1 ^ 3 * a41 * u2 * p2
    - (63772920 : R) * hh * w1 ^ 3 * a41 * q3
    + (623557440 : R) * hh * w1 ^ 3 * p32 * s1 * p2
    - (85030560 : R) * hh * w1 ^ 3 * p32 * q41
    - (106288200 : R) * hh * w1 ^ 3 * q53 * p2
    - (974308500 : R) * hh * w1 ^ 2 * a41 ^ 2 * p32 ^ 2
    + (818419140 : R) * hh * w1 ^ 2 * a41 ^ 2 * p32 * u2
    + (935336160 : R) * hh * w1 ^ 2 * a41 * p32 ^ 2 * s1
    - (318864600 : R) * hh * w1 ^ 2 * a41 * p32 * q53
    - (191318760 : R) * hh * w1 ^ 2 * p32 ^ 2 * b62
    + (212576400 : R) * hh * w1 ^ 2 * p32 ^ 2 * p2
    - (446410440 : R) * hh * w1 ^ 2 * p32 * u2 * p2
    + (71744535 : R) * hh * w1 ^ 2 * p32 * q3
    + (460582200 : R) * hh * w1 * a41 ^ 3 * p1
    - (510183360 : R) * hh * w1 * a41 ^ 2 * s1 * p1
    + (460582200 : R) * hh * w1 * a41 * p32 ^ 3
    - (446410440 : R) * hh * w1 * a41 * p32 ^ 2 * u2
    + (286978140 : R) * hh * w1 * a41 * b62 * p1
    - (558013050 : R) * hh * w1 * a41 * p2 * p1
    - (170061120 : R) * hh * w1 * p32 ^ 3 * s1
    + (119574225 : R) * hh * w1 * p32 ^ 2 * q53
    + (382637520 : R) * hh * w1 * s1 * p2 * p1
    - (114791256 : R) * hh * w1 * p1 * q41
    - (637729200 : R) * hh * a41 ^ 2 * p32 * p1
    + (167403915 : R) * hh * a41 ^ 2 * u2 * p1
    - (28697814 : R) * hh * a41 ^ 2 * q2
    + (382637520 : R) * hh * a41 * p32 * s1 * p1
    - (143489070 : R) * hh * a41 * q53 * p1
    - (53144100 : R) * hh * p32 ^ 4
    + (55801305 : R) * hh * p32 ^ 3 * u2
    - (172186884 : R) * hh * p32 * b62 * p1
    + (478296900 : R) * hh * p32 * p2 * p1
    - (200884698 : R) * hh * u2 * p2 * p1
    + (86093442 : R) * hh * p2 * q2
    + (129140163 : R) * hh * p1 * q3
    - (257650470 : R) * hh * lam * w1 ^ 3 * a41 ^ 4
    + (545612760 : R) * hh * lam * w1 ^ 3 * a41 ^ 2 * p2
    - (116917020 : R) * hh * lam * w1 ^ 3 * p2 ^ 2
    + (545612760 : R) * hh * lam * w1 ^ 2 * a41 ^ 3 * p32
    - (701502120 : R) * hh * lam * w1 ^ 2 * a41 * p32 * p2
    - (350751060 : R) * hh * lam * w1 * a41 ^ 2 * p32 ^ 2
    + (191318760 : R) * hh * lam * w1 * p32 ^ 2 * p2
    + (63772920 : R) * hh * lam * a41 ^ 3 * p1
    + (63772920 : R) * hh * lam * a41 * p32 ^ 3
    - (143489070 : R) * hh * lam * a41 * p2 * p1
    - (254469600 : R) * hh ^ 2 * w1 ^ 6 * a41 ^ 3
    - (458045280 : R) * hh ^ 2 * w1 ^ 6 * a41 ^ 2 * s1
    + (103060188 : R) * hh ^ 2 * w1 ^ 6 * a41 * b62
    + (400789620 : R) * hh ^ 2 * w1 ^ 6 * a41 * p2
    + (137413584 : R) * hh ^ 2 * w1 ^ 6 * s1 * p2
    - (12124728 : R) * hh ^ 2 * w1 ^ 6 * q41
    + (429417450 : R) * hh ^ 2 * w1 ^ 5 * a41 ^ 2 * p32
    + (360710658 : R) * hh ^ 2 * w1 ^ 5 * a41 ^ 2 * u2
    + (824481504 : R) * hh ^ 2 * w1 ^ 5 * a41 * p32 * s1
    - (90935460 : R) * hh ^ 2 * w1 ^ 5 * a41 * q53
    - (109122552 : R) * hh ^ 2 * w1 ^ 5 * p32 * b62
    - (333430020 : R) * hh ^ 2 * w1 ^ 5 * p32 * p2
    - (127309644 : R) * hh ^ 2 * w1 ^ 5 * u2 * p2
    + (11691702 : R) * hh ^ 2 * w1 ^ 5 * q3
    - (151559100 : R) * hh ^ 2 * w1 ^ 4 * a41 * p32 ^ 2
    - (636548220 : R) * hh ^ 2 * w1 ^ 4 * a41 * p32 * u2
    - (363741840 : R) * hh ^ 2 * w1 ^ 4 * p32 ^ 2 * s1
    + (97430850 : R) * hh ^ 2 * w1 ^ 4 * p32 * q53
    - (64953900 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p1
    + (623557440 : R) * hh ^ 2 * w1 ^ 3 * a41 * s1 * p1
    - (21651300 : R) * hh ^ 2 * w1 ^ 3 * p32 ^ 3
    + (272806380 : R) * hh ^ 2 * w1 ^ 3 * p32 ^ 2 * u2
    - (127545840 : R) * hh ^ 2 * w1 ^ 3 * b62 * p1
    - (177147000 : R) * hh ^ 2 * w1 ^ 3 * p2 * p1
    + (425152800 : R) * hh ^ 2 * w1 ^ 2 * a41 * p32 * p1
    - (446410440 : R) * hh ^ 2 * w1 ^ 2 * a41 * u2 * p1
    + (47829690 : R) * hh ^ 2 * w1 ^ 2 * a41 * q2
    - (510183360 : R) * hh ^ 2 * w1 ^ 2 * p32 * s1 * p1
    + (119574225 : R) * hh ^ 2 * w1 ^ 2 * q53 * p1
    - (279006525 : R) * hh ^ 2 * w1 * p32 ^ 2 * p1
    + (334807830 : R) * hh ^ 2 * w1 * p32 * u2 * p1
    - (57395628 : R) * hh ^ 2 * w1 * p32 * q2
    - (212576400 : R) * hh ^ 2 * a41 ^ 3 * p0
    + (191318760 : R) * hh ^ 2 * a41 ^ 2 * s1 * p0
    - (172186884 : R) * hh ^ 2 * a41 * b62 * p0
    + (478296900 : R) * hh ^ 2 * a41 * p2 * p0
    + (239148450 : R) * hh ^ 2 * a41 * p1 ^ 2
    - (229582512 : R) * hh ^ 2 * s1 * p2 * p0
    - (114791256 : R) * hh ^ 2 * s1 * p1 ^ 2
    + (172186884 : R) * hh ^ 2 * p0 * q41
    + (343533960 : R) * hh ^ 2 * lam * w1 ^ 5 * a41 ^ 3
    - (309180564 : R) * hh ^ 2 * lam * w1 ^ 5 * a41 * p2
    - (772951410 : R) * hh ^ 2 * lam * w1 ^ 4 * a41 ^ 2 * p32
    + (272806380 : R) * hh ^ 2 * lam * w1 ^ 4 * p32 * p2
    + (545612760 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 * p32 ^ 2
    - (350751060 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 2 * p1
    - (116917020 : R) * hh ^ 2 * lam * w1 ^ 2 * p32 ^ 3
    + (191318760 : R) * hh ^ 2 * lam * w1 ^ 2 * p2 * p1
    + (382637520 : R) * hh ^ 2 * lam * w1 * a41 * p32 * p1
    - (71744535 : R) * hh ^ 2 * lam * p32 ^ 2 * p1
    + (261285750 : R) * hh ^ 3 * w1 ^ 8 * a41 ^ 2
    + (125417160 : R) * hh ^ 3 * w1 ^ 8 * a41 * s1
    - (12269070 : R) * hh ^ 3 * w1 ^ 8 * b62
    - (88609950 : R) * hh ^ 3 * w1 ^ 8 * p2
    - (463498200 : R) * hh ^ 3 * w1 ^ 7 * a41 * p32
    - (114511320 : R) * hh ^ 3 * w1 ^ 7 * a41 * u2
    - (130870080 : R) * hh ^ 3 * w1 ^ 7 * p32 * s1
    + (12269070 : R) * hh ^ 3 * w1 ^ 7 * q53
    + (200394810 : R) * hh ^ 3 * w1 ^ 6 * p32 ^ 2
    + (120236886 : R) * hh ^ 3 * w1 ^ 6 * p32 * u2
    - (333430020 : R) * hh ^ 3 * w1 ^ 5 * a41 * p1
    - (145496736 : R) * hh ^ 3 * w1 ^ 5 * s1 * p1
    + (259815600 : R) * hh ^ 3 * w1 ^ 4 * p32 * p1
    + (136403190 : R) * hh ^ 3 * w1 ^ 4 * u2 * p1
    - (10628820 : R) * hh ^ 3 * w1 ^ 4 * q2
    + (212576400 : R) * hh ^ 3 * w1 ^ 2 * a41 ^ 2 * p0
    - (510183360 : R) * hh ^ 3 * w1 ^ 2 * a41 * s1 * p0
    + (143489070 : R) * hh ^ 3 * w1 ^ 2 * b62 * p0
    + (79716150 : R) * hh ^ 3 * w1 ^ 2 * p2 * p0
    + (39858075 : R) * hh ^ 3 * w1 ^ 2 * p1 ^ 2
    - (558013050 : R) * hh ^ 3 * w1 * a41 * p32 * p0
    + (334807830 : R) * hh ^ 3 * w1 * a41 * u2 * p0
    - (28697814 : R) * hh ^ 3 * w1 * a41 * q1
    + (382637520 : R) * hh ^ 3 * w1 * p32 * s1 * p0
    - (143489070 : R) * hh ^ 3 * w1 * q53 * p0
    + (239148450 : R) * hh ^ 3 * p32 ^ 2 * p0
    - (200884698 : R) * hh ^ 3 * p32 * u2 * p0
    + (43046721 : R) * hh ^ 3 * p32 * q1
    - (188125740 : R) * hh ^ 3 * lam * w1 ^ 7 * a41 ^ 2
    + (49076280 : R) * hh ^ 3 * lam * w1 ^ 7 * p2
    + (343533960 : R) * hh ^ 3 * lam * w1 ^ 6 * a41 * p32
    - (154590282 : R) * hh ^ 3 * lam * w1 ^ 5 * p32 ^ 2
    + (272806380 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 * p1
    - (233834040 : R) * hh ^ 3 * lam * w1 ^ 3 * p32 * p1
    + (191318760 : R) * hh ^ 3 * lam * w1 * a41 ^ 2 * p0
    - (143489070 : R) * hh ^ 3 * lam * w1 * p2 * p0
    - (71744535 : R) * hh ^ 3 * lam * w1 * p1 ^ 2
    - (143489070 : R) * hh ^ 3 * lam * a41 * p32 * p0
    - (80514720 : R) * hh ^ 4 * w1 ^ 10 * a41
    - (12077208 : R) * hh ^ 4 * w1 ^ 10 * s1
    + (84192075 : R) * hh ^ 4 * w1 ^ 9 * p32
    + (12193335 : R) * hh ^ 4 * w1 ^ 9 * u2
    + (94062870 : R) * hh ^ 4 * w1 ^ 7 * p1
    + (259815600 : R) * hh ^ 4 * w1 ^ 4 * a41 * p0
    + (155889360 : R) * hh ^ 4 * w1 ^ 4 * s1 * p0
    - (177147000 : R) * hh ^ 4 * w1 ^ 3 * p32 * p0
    - (148803480 : R) * hh ^ 4 * w1 ^ 3 * u2 * p0
    + (7971615 : R) * hh ^ 4 * w1 ^ 3 * q1
    + (47829690 : R) * hh ^ 4 * w1 * p1 * p0
    + (45289530 : R) * hh ^ 4 * lam * w1 ^ 9 * a41
    - (47031435 : R) * hh ^ 4 * lam * w1 ^ 8 * p32
    - (51530094 : R) * hh ^ 4 * lam * w1 ^ 6 * p1
    - (233834040 : R) * hh ^ 4 * lam * w1 ^ 3 * a41 * p0
    + (191318760 : R) * hh ^ 4 * lam * w1 ^ 2 * p32 * p0
    + (86093442 : R) * hh ^ 4 * lam * p1 * p0
    + (8107385 : R) * hh ^ 5 * w1 ^ 12
    - (101039400 : R) * hh ^ 5 * w1 ^ 6 * p0
    - (143489070 : R) * hh ^ 5 * p0 ^ 2
    - (3979989 : R) * hh ^ 5 * lam * w1 ^ 11
    + (54561276 : R) * hh ^ 5 * lam * w1 ^ 5 * p0

end BridgeLambdaJet610

/-! ## Jet factorizations of the cleared `λ` defect -/

section BridgeLambdaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- On the fifteenth-face jet the cleared `λ` defect factors exactly as
`h⁵²` times its factored order-`52` head plus `h` times the tail. -/
theorem bridgeClearedLambdaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedLambdaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 52 *
        (bridgeLambdaJetHead610 p31 u1 q4 +
          h * bridgeLambdaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  simp only [bridgeClearedLambdaDefect610, bridgeLambdaJetHead610,
    bridgeLambdaJetTail610]
  ring

set_option maxHeartbeats 80000000 in
/-- On the globally merged deeper jet the cleared `λ` defect factors
exactly as `h⁵⁴` times its order-`54` head plus `h` times the deep
tail. -/
theorem bridgeClearedLambdaDefect610_deepJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedLambdaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 54 *
        (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 +
          h * bridgeLambdaDeepTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1
            p0 q41 q3 q2 q1 (Polynomial.C lambda)) := by
  simp only [bridgeClearedLambdaDefect610, bridgeLambdaDeepHead610,
    bridgeLambdaDeepTail610]
  ring

/-- Evaluation commutes with the order-`52` head. -/
theorem bridgeLambdaJetHead610_eval
    (p31 u1 q4 : k[X]) (x : k) :
    (bridgeLambdaJetHead610 p31 u1 q4).eval x =
      bridgeLambdaJetHead610 (p31.eval x) (u1.eval x) (q4.eval x) := by
  simp only [bridgeLambdaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

/-- Evaluation commutes with the order-`54` head. -/
theorem bridgeLambdaDeepHead610_eval
    (a41 s1 b62 p2 q41 : k[X]) (x : k) :
    (bridgeLambdaDeepHead610 a41 s1 b62 p2 q41).eval x =
      bridgeLambdaDeepHead610 (a41.eval x) (s1.eval x) (b62.eval x)
        (p2.eval x) (q41.eval x) := by
  simp only [bridgeLambdaDeepHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeLambdaJetFactor610

/-! ## Scalar consequences of the vanishing heads -/

section BridgeLambdaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free kill: modulo the tenth-face root laws alone the
vanishing order-`52` head forces `7971615 p₃₁⁴ = 0`, hence
`p₃₁ = 0`. -/
theorem bridgeLambda_chamberFree_kill610
    (p31 u1 q4 : F)
    (hhead : bridgeLambdaJetHead610 p31 u1 q4 = 0)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    p31 = 0 := by
  simp only [bridgeLambdaJetHead610] at hhead
  have h4 : p31 ^ 4 = 0 := by
    linear_combination (1 / 7971615 : F) * hhead -
      (7 / 3 : F) * p31 ^ 3 * hu + (4 / 5 : F) * p31 ^ 2 * hq4
  by_contra hne
  exact pow_ne_zero 4 hne h4

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`54` head modulo
`3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load alone. -/
theorem bridgeLambda_deepReduction610
    (a41 s1 b62 p2 q41 : F)
    (hhead : bridgeLambdaDeepHead610 a41 s1 b62 p2 q41 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 + (30 : F) * p2 = 0) :
    (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0 := by
  simp only [bridgeLambdaDeepHead610] at hhead
  linear_combination (1 / 39366 : F) * hhead -
    (12 : F) * a41 * ((22 : F) * a41 ^ 4 - (120 : F) * a41 ^ 2 * p2 +
      (135 : F) * p2 ^ 2) * hs -
    (9 / 2 : F) * ((10 : F) * a41 ^ 4 - (45 : F) * a41 ^ 2 * p2 +
      (27 : F) * p2 ^ 2) * hU

set_option maxHeartbeats 4000000 in
/-- On the sibling child the retained `q₄₁` tie reduces the
chamber-free sextic relation to `10 a₄₁⁶ - 99 a₄₁⁴ p₂ + 324 a₄₁² p₂²
- 324 p₂³ = 0`; the `a₄₁ = 0` branch forces `p₂ = 0` and the quartic
branch is killed by the resultant certificate `167832 p₂⁴`, so the
child collapses to `a₄₁ = 0 ∧ p₂ = 0`. -/
theorem bridgeLambda_siblingCollapse610
    (a41 p2 q41 : F)
    (hG : (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0)
    (hq41 : (81 : F) * q41 - (90 : F) * a41 * p2 +
      (5 : F) * a41 ^ 3 = 0)
    (hsplit : a41 = 0 ∨
      (4 : F) * a41 ^ 4 - (35 : F) * p2 * a41 ^ 2 +
        (90 : F) * p2 ^ 2 = 0) :
    a41 = 0 ∧ p2 = 0 := by
  have hf1 : (10 : F) * a41 ^ 6 - (99 : F) * a41 ^ 4 * p2 +
      (324 : F) * a41 ^ 2 * p2 ^ 2 - (324 : F) * p2 ^ 3 = 0 := by
    linear_combination (1 / 5 : F) * hG -
      (2 / 5 : F) * a41 * ((5 : F) * a41 ^ 2 - (18 : F) * p2) * hq41
  rcases hsplit with ha41 | hquart
  · refine ⟨ha41, ?_⟩
    have hp3 : p2 ^ 3 = 0 := by
      linear_combination (-(1 : F) / 324) * hf1 +
        (((10 : F) * a41 ^ 5 - (99 : F) * a41 ^ 3 * p2 +
          (324 : F) * a41 * p2 ^ 2) / 324) * ha41
    by_contra hne
    exact pow_ne_zero 3 hne hp3
  · have hp4 : p2 ^ 4 = 0 := by
      linear_combination
        (((52 : F) * a41 ^ 2 - (2543 : F) * p2) / 167832) * hf1 +
        ((-(130 : F) * a41 ^ 4 + (6507 : F) * a41 ^ 2 * p2 -
          (7290 : F) * p2 ^ 2) / 167832) * hquart
    have hp2z : p2 = 0 := by
      by_contra hne
      exact pow_ne_zero 4 hne hp4
    have ha4 : a41 ^ 4 = 0 := by
      linear_combination (1 / 4 : F) * hquart +
        (((35 : F) * a41 ^ 2 - (90 : F) * p2) / 4) * hp2z
    have ha41z : a41 = 0 := by
      by_contra hne
      exact pow_ne_zero 4 hne ha4
    exact ⟨ha41z, hp2z⟩

set_option maxHeartbeats 4000000 in
/-- On the pinned complement child the chamber-free sextic relation
factors as `a₄₁³ (324 q₄₁ - 35 a₄₁³) = 0` — the honest split
`a₄₁ = 0 ∨ 324 q₄₁ = 35 a₄₁³`. -/
theorem bridgeLambda_complementSplit610
    (a41 p2 q41 : F)
    (hG : (100 : F) * a41 ^ 6 - (1575 : F) * a41 ^ 4 * p2 +
        (810 : F) * a41 ^ 3 * q41 + (4860 : F) * a41 ^ 2 * p2 ^ 2 -
      (2916 : F) * a41 * p2 * q41 - (1620 : F) * p2 ^ 3 = 0)
    (hpin : (6 : F) * p2 - a41 ^ 2 = 0) :
    a41 = 0 ∨ (324 : F) * q41 = (35 : F) * a41 ^ 3 := by
  have hprod : a41 ^ 3 * ((324 : F) * q41 - (35 : F) * a41 ^ 3) = 0 := by
    linear_combination hG +
      ((3 : F) * a41 * ((5 : F) * a41 ^ 3 + (162 : F) * q41) -
        (225 / 2 : F) * a41 ^ 2 * ((6 : F) * p2 - a41 ^ 2) +
        (15 / 2 : F) * ((6 : F) * p2 - a41 ^ 2) ^ 2) * hpin
  rcases mul_eq_zero.mp hprod with h3 | hlin
  · left
    by_contra hne
    exact pow_ne_zero 3 hne h3
  · right
    linear_combination hlin

end BridgeLambdaScalars610

/-! ## Finite local lambda integral bridge packet -/

section NonzeroLambdaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `λ` integral bridge: the `κ` bridge packet (the `ι`
and `κ` packets reused opaquely) together with the weight-`60`
clearing of the degree-`3` first integral, its `h₀⁵²`-peeled factored
head, the chamber-free kill `p₃₁(a) = 0` (eliminating the
`p₃₁(a) ≠ 0` complement child by honest contradiction), the globally
merged deeper jet `p₃ = h₀² p₃₂`, `q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`,
`q₄ = h₀ q₄₁`, the `h₀⁵⁴`-peeled deep head with its chamber-free
sextic relation, the collapsed sibling child
`a₄₁(a) = p₂(a) = 0` with its cascade, and the pinned complement
child with the honest split `a₄₁(a) = 0 ∨ 324 q₄₁(a) = 35 a₄₁(a)³`.
Neither surviving child is closed. -/
theorem nonzeroFace610_linearRoot_lambdaIntegralBridge
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a41 s1 u1 p31 b62 q52 p32 u2 q53 q41 : k[X])
      (iotaK kappaMu lambdaNu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C lambdaNu * h0 ^ 60 ∧
        bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
            h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 8 ∧
        bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
          ((q.coeff 4).eval a) = 0 ∧
        p31.eval a = 0 ∧ u1.eval a = 0 ∧ q52.eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
        p.coeff 3 = h0 ^ 2 * p32 ∧ q.coeff 7 = h0 ^ 6 * u2 ∧
        q.coeff 5 = h0 ^ 3 * q53 ∧ q.coeff 4 = h0 * q41 ∧
        bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 6 ∧
        bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 ∧
        (100 : k) * (a41.eval a) ^ 6 -
            (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
          (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
            (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
          (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
            (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 ∧
        ((bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
              h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                (Polynomial.C lambda) =
            Polynomial.C iotaK * h0 ^ 5 ∧
          a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
          s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
          q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          (3 : k) * u2.eval a = (5 : k) * p32.eval a) ∨
        ((6 : k) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
          (6 : k) * b62.eval a - (5 : k) * (a41.eval a) ^ 2 = 0 ∧
          ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
              b62.eval a = 0) ∨
            (324 : k) * q41.eval a = (35 : k) * (a41.eval a) ^ 3))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, _hires1, _hires2, hkpow,
    hkpeel, hkheadeval, _hksplit0, _hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨lambdaNu, hlpow⟩ :=
    nonzeroFace610_bridgeLambdaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hlpowJet :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hlpow
  have hlpeel :
      bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
          h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 8 := by
    have h52 : (h0 : k[X]) ^ 52 ≠ 0 := pow_ne_zero 52 hh0
    apply mul_left_cancel₀ h52
    rw [← bridgeClearedLambdaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowJet]
    ring
  have hlheadeval :
      bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
        ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hlpeel
    have h8z : (0 : k) ^ 8 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaJetHead610_eval, h8z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hp31z : p31.eval a = 0 :=
    bridgeLambda_chamberFree_kill610 (p31.eval a) (u1.eval a)
      ((q.coeff 4).eval a) hlheadeval hTu hWq
  have h3ne : (3 : k) ≠ 0 := by norm_num
  have h9ne : (9 : k) ≠ 0 := by norm_num
  have hu1z : u1.eval a = 0 := by
    have h30 : (3 : k) * u1.eval a = 0 := by
      rw [hTu, hp31z]
      ring
    exact (mul_eq_zero.mp h30).resolve_left h3ne
  have hq52z : q52.eval a = 0 := by
    have h90 : (9 : k) * q52.eval a = 0 := by
      rw [hVq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  have hq4z : (q.coeff 4).eval a = 0 := by
    have h90 : (9 : k) * (q.coeff 4).eval a = 0 := by
      rw [hWq, hp31z]
      ring
    exact (mul_eq_zero.mp h90).resolve_left h9ne
  obtain ⟨p32, hp32⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 p31 a hh0degree hroot
      hp31z
  obtain ⟨u2, hu2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree hroot
      hu1z
  obtain ⟨q53, hq53⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 q52 a hh0degree hroot
      hq52z
  obtain ⟨q41, hq41⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 4) a
      hh0degree hroot hq4z
  have hp3' : p.coeff 3 = h0 ^ 2 * p32 := by
    rw [hp3, hp32]
    ring
  have hq7' : q.coeff 7 = h0 ^ 6 * u2 := by
    rw [hu, hu2]
    ring
  have hq5' : q.coeff 5 = h0 ^ 3 * q53 := by
    rw [hq5, hq53]
    ring
  have hq4' : q.coeff 4 = h0 * q41 := hq41
  have hlpowDeep :
      bridgeClearedLambdaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C lambdaNu * h0 ^ 60 := by
    rw [← hw, ← ha4s, ← hp3', ← hs, ← hq7', ← hb6s, ← hq5', ← hq4']
    exact hlpow
  have hldeepPeel :
      bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
          h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
            (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C lambdaNu * h0 ^ 6 := by
    have h54 : (h0 : k[X]) ^ 54 ≠ 0 := pow_ne_zero 54 hh0
    apply mul_left_cancel₀ h54
    rw [← bridgeClearedLambdaDefect610_deepJet_factored h0 w1 a41 p32
      s1 u2 b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hlpowDeep]
    ring
  have hldeepHeadEval :
      bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
        ((p.coeff 2).eval a) (q41.eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hldeepPeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeLambdaDeepHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hUz : (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
      (30 : k) * (p.coeff 2).eval a = 0 := by
    linear_combination hUload +
      ((9 : k) * lambda - (20 : k) * w1.eval a) * hp31z
  have hG :
      (100 : k) * (a41.eval a) ^ 6 -
          (1575 : k) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
        (810 : k) * (a41.eval a) ^ 3 * q41.eval a +
          (4860 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
        (2916 : k) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
          (1620 : k) * ((p.coeff 2).eval a) ^ 3 = 0 :=
    bridgeLambda_deepReduction610 (a41.eval a) (s1.eval a)
      (b62.eval a) ((p.coeff 2).eval a) (q41.eval a) hldeepHeadEval
      hMs hUz
  refine ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs, hUload,
    hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG, ?_⟩
  rcases halt with ⟨-, p32', u2', q53', q41', hp3s, hq7s, hq5s, hq4s,
      hrel1, hrel2, hrel3, hrel4, hileft, -, hsplit⟩ |
    ⟨-, -, hcd⟩
  · have hp32e : p32' = p32 :=
      mul_left_cancel₀ (pow_ne_zero 2 hh0) (hp3s.symm.trans hp3')
    have hu2e : u2' = u2 :=
      mul_left_cancel₀ (pow_ne_zero 6 hh0) (hq7s.symm.trans hq7')
    have hq53e : q53' = q53 :=
      mul_left_cancel₀ (pow_ne_zero 3 hh0) (hq5s.symm.trans hq5')
    have hq41e : q41' = q41 :=
      mul_left_cancel₀ hh0 (hq4s.symm.trans hq4')
    simp only [hp32e, hu2e, hq53e, hq41e] at hrel1 hrel2 hrel3 hrel4 hileft
    obtain ⟨ha41z, hp2z⟩ :=
      bridgeLambda_siblingCollapse610 (a41.eval a)
        ((p.coeff 2).eval a) (q41.eval a) hG hrel2 hsplit
    have hs1z : s1.eval a = 0 := by
      have h30 : (3 : k) * s1.eval a = 0 := by
        rw [hMs, ha41z]
        ring
      exact (mul_eq_zero.mp h30).resolve_left h3ne
    have hb62z : b62.eval a = 0 := by
      linear_combination (-(1 : k) / 18) * hUz +
        ((5 : k) / 9) * a41.eval a * ha41z + ((5 : k) / 3) * hp2z
    have hq41z : q41.eval a = 0 := by
      linear_combination ((1 : k) / 81) * hrel2 +
        (((10 : k) / 9) * (p.coeff 2).eval a -
          ((5 : k) / 81) * (a41.eval a) ^ 2) * ha41z
    have hq53z : q53.eval a = 0 := by
      linear_combination ((1 : k) / 216) * hrel3 +
        (-(lambda * a41.eval a) / 8 -
          ((5 : k) / 27) * a41.eval a * w1.eval a +
          ((10 : k) / 9) * p32.eval a) * ha41z +
        (-lambda / 2 + ((10 : k) / 9) * w1.eval a) * hp2z
    have hq3z : (q.coeff 3).eval a = 0 := by
      linear_combination ((1 : k) / 3888) * hrel4 +
        (lambda * (a41.eval a) ^ 2 / 48 +
          ((20 : k) / 243) * (a41.eval a) ^ 2 * w1.eval a -
          ((5 : k) / 27) * a41.eval a * p32.eval a -
          lambda * (p.coeff 2).eval a / 4 -
          ((10 : k) / 27) * (p.coeff 2).eval a * w1.eval a) * ha41z +
        ((10 : k) / 9) * p32.eval a * hp2z
    have hu2tie : (3 : k) * u2.eval a = (5 : k) * p32.eval a := by
      linear_combination ((1 : k) / 6) * hrel1 +
        (((10 : k) / 3) * w1.eval a - ((3 : k) / 2) * lambda) * ha41z
    exact Or.inl ⟨hileft, ha41z, hp2z, hs1z, hb62z, hq41z, hq53z,
      hq3z, hu2tie⟩
  · rcases hcd with ⟨-, hp2pin, hb62pin⟩ | ⟨hnz, -⟩
    · refine Or.inr ⟨hp2pin, hb62pin, ?_⟩
      rcases bridgeLambda_complementSplit610 (a41.eval a)
          ((p.coeff 2).eval a) (q41.eval a) hG hp2pin with
        ha41z | hq41pin
      · left
        have hp2z : (p.coeff 2).eval a = 0 := by
          linear_combination ((1 : k) / 6) * hp2pin +
            ((1 : k) / 6) * a41.eval a * ha41z
        have hb62z : b62.eval a = 0 := by
          linear_combination ((1 : k) / 6) * hb62pin +
            ((5 : k) / 6) * a41.eval a * ha41z
        exact ⟨ha41z, hp2z, hb62z⟩
      · exact Or.inr hq41pin
    · exact absurd hp31z hnz

set_option maxHeartbeats 40000000 in
/-- Source-facing `λ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the `κ` bridge packet with the weight-`60`
clearing of the degree-`3` first integral, the chamber-free kill
`p₃₁(a) = 0` eliminating the `p₃₁(a) ≠ 0` complement child, the
globally merged deeper jet, the `h₀⁵⁴`-peeled deep head with its
chamber-free sextic relation, the collapsed sibling child
`a₄₁(a) = p₂(a) = 0` with its cascade, and the pinned complement
child with the honest split `a₄₁(a) = 0 ∨ 324 q₄₁(a) = 35 a₄₁(a)³`.
The ground constants `iotaK`, `kappaMu` and `lambdaNu` are preserved,
not cleared, and neither surviving child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_lambdaIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu lambdaNu : K)
      (w1 a41 s1 u1 p31 b62 q52 p32 u2 q53 q41 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        p.coeff 3 = h0 ^ 2 * p32 ∧ q.coeff 7 = h0 ^ 6 * u2 ∧
        q.coeff 5 = h0 ^ 3 * q53 ∧ q.coeff 4 = h0 * q41 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 3 ∣ q.coeff 5 ∧ h0 ∣ q.coeff 4 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
        p31.eval a = 0 ∧ u1.eval a = 0 ∧ q52.eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
        jK ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C lambdaNu * h0 ^ 60 ∧
        bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
            h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 8 ∧
        bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
          ((q.coeff 4).eval a) = 0 ∧
        bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 6 ∧
        bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 ∧
        (100 : K) * (a41.eval a) ^ 6 -
            (1575 : K) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
          (810 : K) * (a41.eval a) ^ 3 * q41.eval a +
            (4860 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
          (2916 : K) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
            (1620 : K) * ((p.coeff 2).eval a) ^ 3 = 0 ∧
        ((bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
              h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                (Polynomial.C lambda) =
            Polynomial.C iotaK * h0 ^ 5 ∧
          a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
          s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
          q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
          (3 : K) * u2.eval a = (5 : K) * p32.eval a) ∨
        ((6 : K) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
          (6 : K) * b62.eval a - (5 : K) * (a41.eval a) ^ 2 = 0 ∧
          ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
              b62.eval a = 0) ∨
            (324 : K) * q41.eval a = (35 : K) * (a41.eval a) ^ 3))) ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w1, a41, s1, u1, p31, b62, q52, hh0, hlambda,
    hh0degree, hH, hroot, hw, ha4s, hp3, hs, hu, hb6s, hq5, hq9, hp5d,
    hp4d, hp3d, hq8d, hq7d, hq6d, hq5d, hMs, hTu, hVq, hWq, hUload,
    hXalt, hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_tenthPowerJet hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', p32', u2', q53',
    q41', iotaK, kappaMu, lambdaNu, hwN, ha4sN, hp3N, hsN, huN,
    hb6sN, hq5N, hMs', hUload', hrow, hroweval, hipow, hipeel,
    hiheadeval, hkpow, hkpeel, hkheadeval, hlpow, hlpeel, hlheadeval,
    hp31z, hu1z, hq52z, hq4z, hp3deep, hq7deep, hq5deep, hq4deep,
    hldeepPeel, hldeepHeadEval, hG, halt⟩ :=
    nonzeroFace610_linearRoot_lambdaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, lambdaNu, w1', a41', s1',
    u1', p31', b62', q52', p32', u2', q53', q41', hh0, hlambda,
    hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN, huN, hb6sN, hq5N,
    hp3deep, hq7deep, hq5deep, hq4deep, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3deep]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [hq7deep]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5deep]; exact dvd_mul_right _ _),
    (by rw [hq4deep]; exact dvd_mul_right _ _),
    hMs', hUload', hp31z, hu1z, hq52z, hq4z, hj, hrow, hroweval, hsep,
    hipow, hipeel, hiheadeval, hkpow, hkpeel, hkheadeval, hlpow,
    hlpeel, hlheadeval, hldeepPeel, hldeepHeadEval, hG, halt, hN'⟩

end NonzeroLambdaIntegralBridge610

#print axioms nonzeroFace610_linearRoot_lambdaIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_lambdaIntegralBridge

#print axioms nonzeroFace610_bridgeLambdaPowerRelation

end Max11DegreeRoutes
