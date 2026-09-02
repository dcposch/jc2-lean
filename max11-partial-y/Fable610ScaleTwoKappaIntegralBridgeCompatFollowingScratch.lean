import Fable610ScaleTwoKappaIntegralBridgeCompatNextScratch

/-! # Mu integral bridge continuation for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h₀²` and `N = 5 p₅ H² - 3 q₉ = λ h₀⁹`
with `h₀.natDegree = 1`, the compatible `λ` bridge spent the degree-`3`
first integral; the next genuinely unused integral row is the
degree-`2` first integral `μ`, the weight-thirteen constant of the
depressed flow.  Its construction is the first on this chain that is
not separable from a lower row: the degree-`2` and degree-`4` rows are
tied through the non-constant multiplier `A/12`, so the derivation
identity is `d μ = (1/6)·row₂ - (1/12)·A·row₄` — no polynomial
normalization can remove the `row₄` load, because the obstruction
`κ · dA` is not exact.  The scale-zero scratches state nothing at this
weight; the residual, its derivation reduction, and the weight-`65`
clearing `bridgeClearedMuDefect610 = C muXi · h₀⁶⁵` (multiplier
`12582912 = 2²² · 3`, first seeing `q₁`, never `q₀`) are derived from
the source differential rows already in the canonical ancestry (rows
`13` through `7`, the bridge rows `6`, `5` and `4`, and the degree-`2`
row stated here).  The spent `ι`, `κ` and `λ` packets are reused
opaquely; none of the weight-`50`/`55`/`60` numerators is ever
re-expanded.

On the globally merged jet `p₅ = h₀⁵ w₁`, `p₄ = h₀³ a₄₁`,
`p₃ = h₀² p₃₂`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁶ u₂`, `q₆ = h₀⁴ b₆₂`,
`q₅ = h₀³ q₅₃`, `q₄ = h₀ q₄₁` the numerator factors exactly through
`h₀⁵⁹`, six orders below the defect weight, with content-`4096` head;
modulo the root laws `3 s₁ = 5 a₄₁` and the `p₃₁`-killed `U`-load
alone the vanishing head reduces, chamber-free, to a
twenty-three-term relation that every `a₄₁(a) = p₂(a) = 0` child
absorbs identically.  On the pinned complement child with the `q`-jet
pin `324 q₄₁ = 35 a₄₁³` it factors as `a₄₁³ · G = 0` — the honest
split `a₄₁(a) = 0` (which collapses that child onto
`a₄₁(a) = p₂(a) = b₆₂(a) = q₄₁(a) = 0`) or the first `q₃`-tie on that
child, `15552 q₃(a) = -2943 λ a₄₁³ + 14040 a₄₁³ w₁ + 1060 a₄₁² p₃₂
- 11340 a₄₁² u₂ + 14040 a₄₁ q₅₃` at the root.

On the collapsed sibling child the seven root kills upgrade to the
divisibilities `p₄ = h₀⁴ a₄₂`, `p₂ = h₀ p₂₁`, `q₈ = h₀⁸ s₂`,
`q₆ = h₀⁵ b₆₃`, `q₅ = h₀⁴ q₅₄`, `q₄ = h₀² q₄₂`, `q₃ = h₀ q₃₁`, and
the re-substituted numerator factors two orders deeper, through
`h₀⁶¹`, with head `32768 p₃₂ · F`: the honest split `p₃₂(a) = 0`
(whence `u₂(a) = 0`) or the first `λ`-loaded tie on the quotient jet,
`144 b₆₃ p₃₂² + 45 λ p₃₂³ + 240 p₂₁ p₃₂² - 384 p₂₁ q₄₂ - 400 p₃₂³ w₁
- 144 p₃₂ q₃₁ + 288 p₃₂ q₄₂ w₁ = 0` at the root — the first relation
of the tower seeing the `p₂`-quotient `p₂₁`.

No child is closed, because none is contradicted — the inhomogeneous
Keller boundary row `p₀'(a) q₁(a) - p₁(a) q₀'(a) = j ≠ 0` lives on
the fresh coordinates `p₀, p₁, q₀, q₁` the `h`-adic jet does not
control, and the `μ` head never reaches them.  The honest residual is
that single boundary relation, the refined children, the preserved
ground constants `ζ, η, iotaK, kappaMu, lambdaNu, muXi`, and the open
aligned face `N = 0`.  The next unused integral row is the degree-`1`
first integral; the next unused aligned row on `N = 0` is the
degree-`10` row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Degree-`2` residual and its weight-`65` clearing -/

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

set_option maxHeartbeats 8000000 in
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

set_option maxHeartbeats 800000000 in
/-- Clearing the first integral `μ` of the degree-`2` row against `h⁶⁵`
on the ninth-power face. -/
theorem bridgeMuDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (12582912 : F) * h ^ 65 *
        bridgeMuResidual610
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
    - (180880 : F) * a5 ^ 13
    + (88179 : F) * a5 ^ 12 * lambda * h ^ 5
    + (2015520 : F) * a5 ^ 11 * a4 * h ^ 6
    + (268736 : F) * a5 ^ 11 * b8 * h ^ 2
    - (1108536 : F) * a5 ^ 10 * a4 * lambda * h ^ 11
    - (2139280 : F) * a5 ^ 10 * a3 * h ^ 12
    - (272272 : F) * a5 ^ 10 * b7 * h ^ 8
    - (7779200 : F) * a5 ^ 9 * a4 ^ 2 * h ^ 12
    - (3111680 : F) * a5 ^ 9 * a4 * b8 * h ^ 8
    + (1166880 : F) * a5 ^ 9 * a3 * lambda * h ^ 17
    + (2288000 : F) * a5 ^ 9 * a2 * h ^ 18
    + (274560 : F) * a5 ^ 9 * b6 * h ^ 14
    + (5250960 : F) * a5 ^ 8 * a4 ^ 2 * lambda * h ^ 17
    + (14414400 : F) * a5 ^ 8 * a4 * a3 * h ^ 18
    + (2882880 : F) * a5 ^ 8 * a4 * b7 * h ^ 14
    + (3294720 : F) * a5 ^ 8 * a3 * b8 * h ^ 14
    - (1235520 : F) * a5 ^ 8 * a2 * lambda * h ^ 23
    - (2471040 : F) * a5 ^ 8 * a1 * h ^ 24
    - (274560 : F) * a5 ^ 8 * b5 * h ^ 20
    + (10982400 : F) * a5 ^ 7 * a4 ^ 3 * h ^ 18
    + (13178880 : F) * a5 ^ 7 * a4 ^ 2 * b8 * h ^ 14
    - (9884160 : F) * a5 ^ 7 * a4 * a3 * lambda * h ^ 23
    - (13178880 : F) * a5 ^ 7 * a4 * a2 * h ^ 24
    - (2635776 : F) * a5 ^ 7 * a4 * b6 * h ^ 20
    - (6589440 : F) * a5 ^ 7 * a3 ^ 2 * h ^ 24
    - (3075072 : F) * a5 ^ 7 * a3 * b7 * h ^ 20
    - (3514368 : F) * a5 ^ 7 * a2 * b8 * h ^ 20
    + (1317888 : F) * a5 ^ 7 * a1 * lambda * h ^ 29
    + (2703360 : F) * a5 ^ 7 * a0 * h ^ 30
    + (270336 : F) * a5 ^ 7 * b4 * h ^ 26
    - (11531520 : F) * a5 ^ 6 * a4 ^ 3 * lambda * h ^ 23
    - (23063040 : F) * a5 ^ 6 * a4 ^ 2 * a3 * h ^ 24
    - (10762752 : F) * a5 ^ 6 * a4 ^ 2 * b7 * h ^ 20
    - (24600576 : F) * a5 ^ 6 * a4 * a3 * b8 * h ^ 20
    + (9225216 : F) * a5 ^ 6 * a4 * a2 * lambda * h ^ 29
    + (11827200 : F) * a5 ^ 6 * a4 * a1 * h ^ 30
    + (2365440 : F) * a5 ^ 6 * a4 * b5 * h ^ 26
    + (4612608 : F) * a5 ^ 6 * a3 ^ 2 * lambda * h ^ 29
    + (11827200 : F) * a5 ^ 6 * a3 * a2 * h ^ 30
    + (2838528 : F) * a5 ^ 6 * a3 * b6 * h ^ 26
    + (3311616 : F) * a5 ^ 6 * a2 * b7 * h ^ 26
    + (3784704 : F) * a5 ^ 6 * a1 * b8 * h ^ 26
    - (1419264 : F) * a5 ^ 6 * a0 * lambda * h ^ 35
    - (258048 : F) * a5 ^ 6 * b3 * h ^ 32
    - (24600576 : F) * a5 ^ 5 * a4 ^ 3 * b8 * h ^ 20
    + (27675648 : F) * a5 ^ 5 * a4 ^ 2 * a3 * lambda * h ^ 29
    + (14192640 : F) * a5 ^ 5 * a4 ^ 2 * a2 * h ^ 30
    + (8515584 : F) * a5 ^ 5 * a4 ^ 2 * b6 * h ^ 26
    + (14192640 : F) * a5 ^ 5 * a4 * a3 ^ 2 * h ^ 30
    + (19869696 : F) * a5 ^ 5 * a4 * a3 * b7 * h ^ 26
    + (22708224 : F) * a5 ^ 5 * a4 * a2 * b8 * h ^ 26
    - (8515584 : F) * a5 ^ 5 * a4 * a1 * lambda * h ^ 35
    - (10321920 : F) * a5 ^ 5 * a4 * a0 * h ^ 36
    - (2064384 : F) * a5 ^ 5 * a4 * b4 * h ^ 32
    + (11354112 : F) * a5 ^ 5 * a3 ^ 2 * b8 * h ^ 26
    - (8515584 : F) * a5 ^ 5 * a3 * a2 * lambda * h ^ 35
    - (10321920 : F) * a5 ^ 5 * a3 * a1 * h ^ 36
    - (2580480 : F) * a5 ^ 5 * a3 * b5 * h ^ 32
    - (5160960 : F) * a5 ^ 5 * a2 ^ 2 * h ^ 36
    - (3096576 : F) * a5 ^ 5 * a2 * b6 * h ^ 32
    - (3612672 : F) * a5 ^ 5 * a1 * b7 * h ^ 32
    - (4128768 : F) * a5 ^ 5 * a0 * b8 * h ^ 32
    + (229376 : F) * a5 ^ 5 * b2 * h ^ 38
    + (11531520 : F) * a5 ^ 4 * a4 ^ 4 * lambda * h ^ 29
    - (11827200 : F) * a5 ^ 4 * a4 ^ 3 * a3 * h ^ 30
    + (16558080 : F) * a5 ^ 4 * a4 ^ 3 * b7 * h ^ 26
    + (56770560 : F) * a5 ^ 4 * a4 ^ 2 * a3 * b8 * h ^ 26
    - (21288960 : F) * a5 ^ 4 * a4 ^ 2 * a2 * lambda * h ^ 35
    - (6451200 : F) * a5 ^ 4 * a4 ^ 2 * a1 * h ^ 36
    - (6451200 : F) * a5 ^ 4 * a4 ^ 2 * b5 * h ^ 32
    - (21288960 : F) * a5 ^ 4 * a4 * a3 ^ 2 * lambda * h ^ 35
    - (12902400 : F) * a5 ^ 4 * a4 * a3 * a2 * h ^ 36
    - (15482880 : F) * a5 ^ 4 * a4 * a3 * b6 * h ^ 32
    - (18063360 : F) * a5 ^ 4 * a4 * a2 * b7 * h ^ 32
    - (20643840 : F) * a5 ^ 4 * a4 * a1 * b8 * h ^ 32
    + (7741440 : F) * a5 ^ 4 * a4 * a0 * lambda * h ^ 41
    + (1720320 : F) * a5 ^ 4 * a4 * b3 * h ^ 38
    - (2150400 : F) * a5 ^ 4 * a3 ^ 3 * h ^ 36
    - (9031680 : F) * a5 ^ 4 * a3 ^ 2 * b7 * h ^ 32
    - (20643840 : F) * a5 ^ 4 * a3 * a2 * b8 * h ^ 32
    + (7741440 : F) * a5 ^ 4 * a3 * a1 * lambda * h ^ 41
    + (8601600 : F) * a5 ^ 4 * a3 * a0 * h ^ 42
    + (2293760 : F) * a5 ^ 4 * a3 * b4 * h ^ 38
    + (3870720 : F) * a5 ^ 4 * a2 ^ 2 * lambda * h ^ 41
    + (8601600 : F) * a5 ^ 4 * a2 * a1 * h ^ 42
    + (2867200 : F) * a5 ^ 4 * a2 * b5 * h ^ 38
    + (3440640 : F) * a5 ^ 4 * a1 * b6 * h ^ 38
    + (4014080 : F) * a5 ^ 4 * a0 * b7 * h ^ 38
    - (163840 : F) * a5 ^ 4 * b1 * h ^ 44
    - (9461760 : F) * a5 ^ 3 * a4 ^ 5 * h ^ 30
    + (18923520 : F) * a5 ^ 3 * a4 ^ 4 * b8 * h ^ 26
    - (28385280 : F) * a5 ^ 3 * a4 ^ 3 * a3 * lambda * h ^ 35
    + (17203200 : F) * a5 ^ 3 * a4 ^ 3 * a2 * h ^ 36
    - (10321920 : F) * a5 ^ 3 * a4 ^ 3 * b6 * h ^ 32
    + (25804800 : F) * a5 ^ 3 * a4 ^ 2 * a3 ^ 2 * h ^ 36
    - (36126720 : F) * a5 ^ 3 * a4 ^ 2 * a3 * b7 * h ^ 32
    - (41287680 : F) * a5 ^ 3 * a4 ^ 2 * a2 * b8 * h ^ 32
    + (15482880 : F) * a5 ^ 3 * a4 ^ 2 * a1 * lambda * h ^ 41
    + (4587520 : F) * a5 ^ 3 * a4 ^ 2 * b4 * h ^ 38
    - (41287680 : F) * a5 ^ 3 * a4 * a3 ^ 2 * b8 * h ^ 32
    + (30965760 : F) * a5 ^ 3 * a4 * a3 * a2 * lambda * h ^ 41
    + (11468800 : F) * a5 ^ 3 * a4 * a3 * b5 * h ^ 38
    + (13762560 : F) * a5 ^ 3 * a4 * a2 * b6 * h ^ 38
    + (16056320 : F) * a5 ^ 3 * a4 * a1 * b7 * h ^ 38
    + (18350080 : F) * a5 ^ 3 * a4 * a0 * b8 * h ^ 38
    - (1310720 : F) * a5 ^ 3 * a4 * b2 * h ^ 44
    + (5160960 : F) * a5 ^ 3 * a3 ^ 3 * lambda * h ^ 41
    + (6881280 : F) * a5 ^ 3 * a3 ^ 2 * b6 * h ^ 38
    + (16056320 : F) * a5 ^ 3 * a3 * a2 * b7 * h ^ 38
    + (18350080 : F) * a5 ^ 3 * a3 * a1 * b8 * h ^ 38
    - (6881280 : F) * a5 ^ 3 * a3 * a0 * lambda * h ^ 47
    - (1966080 : F) * a5 ^ 3 * a3 * b3 * h ^ 44
    + (9175040 : F) * a5 ^ 3 * a2 ^ 2 * b8 * h ^ 38
    - (6881280 : F) * a5 ^ 3 * a2 * a1 * lambda * h ^ 47
    - (6553600 : F) * a5 ^ 3 * a2 * a0 * h ^ 48
    - (2621440 : F) * a5 ^ 3 * a2 * b4 * h ^ 44
    - (3276800 : F) * a5 ^ 3 * a1 ^ 2 * h ^ 48
    - (3276800 : F) * a5 ^ 3 * a1 * b5 * h ^ 44
    - (3932160 : F) * a5 ^ 3 * a0 * b6 * h ^ 44
    - (4257792 : F) * a5 ^ 2 * a4 ^ 5 * lambda * h ^ 35
    + (32256000 : F) * a5 ^ 2 * a4 ^ 4 * a3 * h ^ 36
    - (9031680 : F) * a5 ^ 2 * a4 ^ 4 * b7 * h ^ 32
    - (41287680 : F) * a5 ^ 2 * a4 ^ 3 * a3 * b8 * h ^ 32
    + (15482880 : F) * a5 ^ 2 * a4 ^ 3 * a2 * lambda * h ^ 41
    - (17203200 : F) * a5 ^ 2 * a4 ^ 3 * a1 * h ^ 42
    + (5734400 : F) * a5 ^ 2 * a4 ^ 3 * b5 * h ^ 38
    + (23224320 : F) * a5 ^ 2 * a4 ^ 2 * a3 ^ 2 * lambda * h ^ 41
    - (51609600 : F) * a5 ^ 2 * a4 ^ 2 * a3 * a2 * h ^ 42
    + (20643840 : F) * a5 ^ 2 * a4 ^ 2 * a3 * b6 * h ^ 38
    + (24084480 : F) * a5 ^ 2 * a4 ^ 2 * a2 * b7 * h ^ 38
    + (27525120 : F) * a5 ^ 2 * a4 ^ 2 * a1 * b8 * h ^ 38
    - (10321920 : F) * a5 ^ 2 * a4 ^ 2 * a0 * lambda * h ^ 47
    - (2949120 : F) * a5 ^ 2 * a4 ^ 2 * b3 * h ^ 44
    - (17203200 : F) * a5 ^ 2 * a4 * a3 ^ 3 * h ^ 42
    + (24084480 : F) * a5 ^ 2 * a4 * a3 ^ 2 * b7 * h ^ 38
    + (55050240 : F) * a5 ^ 2 * a4 * a3 * a2 * b8 * h ^ 38
    - (20643840 : F) * a5 ^ 2 * a4 * a3 * a1 * lambda * h ^ 47
    + (9830400 : F) * a5 ^ 2 * a4 * a3 * a0 * h ^ 48
    - (7864320 : F) * a5 ^ 2 * a4 * a3 * b4 * h ^ 44
    - (10321920 : F) * a5 ^ 2 * a4 * a2 ^ 2 * lambda * h ^ 47
    + (9830400 : F) * a5 ^ 2 * a4 * a2 * a1 * h ^ 48
    - (9830400 : F) * a5 ^ 2 * a4 * a2 * b5 * h ^ 44
    - (11796480 : F) * a5 ^ 2 * a4 * a1 * b6 * h ^ 44
    - (13762560 : F) * a5 ^ 2 * a4 * a0 * b7 * h ^ 44
    + (786432 : F) * a5 ^ 2 * a4 * b1 * h ^ 50
    + (9175040 : F) * a5 ^ 2 * a3 ^ 3 * b8 * h ^ 38
    - (10321920 : F) * a5 ^ 2 * a3 ^ 2 * a2 * lambda * h ^ 47
    + (4915200 : F) * a5 ^ 2 * a3 ^ 2 * a1 * h ^ 48
    - (4915200 : F) * a5 ^ 2 * a3 ^ 2 * b5 * h ^ 44
    + (4915200 : F) * a5 ^ 2 * a3 * a2 ^ 2 * h ^ 48
    - (11796480 : F) * a5 ^ 2 * a3 * a2 * b6 * h ^ 44
    - (13762560 : F) * a5 ^ 2 * a3 * a1 * b7 * h ^ 44
    - (15728640 : F) * a5 ^ 2 * a3 * a0 * b8 * h ^ 44
    + (1572864 : F) * a5 ^ 2 * a3 * b2 * h ^ 50
    - (6881280 : F) * a5 ^ 2 * a2 ^ 2 * b7 * h ^ 44
    - (15728640 : F) * a5 ^ 2 * a2 * a1 * b8 * h ^ 44
    + (5898240 : F) * a5 ^ 2 * a2 * a0 * lambda * h ^ 53
    + (2359296 : F) * a5 ^ 2 * a2 * b3 * h ^ 50
    + (2949120 : F) * a5 ^ 2 * a1 ^ 2 * lambda * h ^ 53
    + (3932160 : F) * a5 ^ 2 * a1 * a0 * h ^ 54
    + (3145728 : F) * a5 ^ 2 * a1 * b4 * h ^ 50
    + (3932160 : F) * a5 ^ 2 * a0 * b5 * h ^ 50
    + (3440640 : F) * a5 * a4 ^ 6 * h ^ 36
    - (4128768 : F) * a5 * a4 ^ 5 * b8 * h ^ 32
    + (7741440 : F) * a5 * a4 ^ 4 * a3 * lambda * h ^ 41
    - (17203200 : F) * a5 * a4 ^ 4 * a2 * h ^ 42
    + (3440640 : F) * a5 * a4 ^ 4 * b6 * h ^ 38
    - (34406400 : F) * a5 * a4 ^ 3 * a3 ^ 2 * h ^ 42
    + (16056320 : F) * a5 * a4 ^ 3 * a3 * b7 * h ^ 38
    + (18350080 : F) * a5 * a4 ^ 3 * a2 * b8 * h ^ 38
    - (6881280 : F) * a5 * a4 ^ 3 * a1 * lambda * h ^ 47
    + (13107200 : F) * a5 * a4 ^ 3 * a0 * h ^ 48
    - (2621440 : F) * a5 * a4 ^ 3 * b4 * h ^ 44
    + (27525120 : F) * a5 * a4 ^ 2 * a3 ^ 2 * b8 * h ^ 38
    - (20643840 : F) * a5 * a4 ^ 2 * a3 * a2 * lambda * h ^ 47
    + (39321600 : F) * a5 * a4 ^ 2 * a3 * a1 * h ^ 48
    - (9830400 : F) * a5 * a4 ^ 2 * a3 * b5 * h ^ 44
    + (19660800 : F) * a5 * a4 ^ 2 * a2 ^ 2 * h ^ 48
    - (11796480 : F) * a5 * a4 ^ 2 * a2 * b6 * h ^ 44
    - (13762560 : F) * a5 * a4 ^ 2 * a1 * b7 * h ^ 44
    - (15728640 : F) * a5 * a4 ^ 2 * a0 * b8 * h ^ 44
    + (1572864 : F) * a5 * a4 ^ 2 * b2 * h ^ 50
    - (6881280 : F) * a5 * a4 * a3 ^ 3 * lambda * h ^ 47
    + (39321600 : F) * a5 * a4 * a3 ^ 2 * a2 * h ^ 48
    - (11796480 : F) * a5 * a4 * a3 ^ 2 * b6 * h ^ 44
    - (27525120 : F) * a5 * a4 * a3 * a2 * b7 * h ^ 44
    - (31457280 : F) * a5 * a4 * a3 * a1 * b8 * h ^ 44
    + (11796480 : F) * a5 * a4 * a3 * a0 * lambda * h ^ 53
    + (4718592 : F) * a5 * a4 * a3 * b3 * h ^ 50
    - (15728640 : F) * a5 * a4 * a2 ^ 2 * b8 * h ^ 44
    + (11796480 : F) * a5 * a4 * a2 * a1 * lambda * h ^ 53
    - (15728640 : F) * a5 * a4 * a2 * a0 * h ^ 54
    + (6291456 : F) * a5 * a4 * a2 * b4 * h ^ 50
    - (7864320 : F) * a5 * a4 * a1 ^ 2 * h ^ 54
    + (7864320 : F) * a5 * a4 * a1 * b5 * h ^ 50
    + (9437184 : F) * a5 * a4 * a0 * b6 * h ^ 50
    + (3276800 : F) * a5 * a3 ^ 4 * h ^ 48
    - (4587520 : F) * a5 * a3 ^ 3 * b7 * h ^ 44
    - (15728640 : F) * a5 * a3 ^ 2 * a2 * b8 * h ^ 44
    + (5898240 : F) * a5 * a3 ^ 2 * a1 * lambda * h ^ 53
    - (7864320 : F) * a5 * a3 ^ 2 * a0 * h ^ 54
    + (3145728 : F) * a5 * a3 ^ 2 * b4 * h ^ 50
    + (5898240 : F) * a5 * a3 * a2 ^ 2 * lambda * h ^ 53
    - (15728640 : F) * a5 * a3 * a2 * a1 * h ^ 54
    + (7864320 : F) * a5 * a3 * a2 * b5 * h ^ 50
    + (9437184 : F) * a5 * a3 * a1 * b6 * h ^ 50
    + (11010048 : F) * a5 * a3 * a0 * b7 * h ^ 50
    - (1048576 : F) * a5 * a3 * b1 * h ^ 56
    - (2621440 : F) * a5 * a2 ^ 3 * h ^ 54
    + (4718592 : F) * a5 * a2 ^ 2 * b6 * h ^ 50
    + (11010048 : F) * a5 * a2 * a1 * b7 * h ^ 50
    + (12582912 : F) * a5 * a2 * a0 * b8 * h ^ 50
    - (2097152 : F) * a5 * a2 * b2 * h ^ 56
    + (6291456 : F) * a5 * a1 ^ 2 * b8 * h ^ 50
    - (4718592 : F) * a5 * a1 * a0 * lambda * h ^ 59
    - (3145728 : F) * a5 * a1 * b3 * h ^ 56
    - (4194304 : F) * a5 * a0 * b4 * h ^ 56
    + (258048 : F) * a4 ^ 6 * lambda * h ^ 41
    - (5160960 : F) * a4 ^ 5 * a3 * h ^ 42
    + (802816 : F) * a4 ^ 5 * b7 * h ^ 38
    + (4587520 : F) * a4 ^ 4 * a3 * b8 * h ^ 38
    - (1720320 : F) * a4 ^ 4 * a2 * lambda * h ^ 47
    + (5734400 : F) * a4 ^ 4 * a1 * h ^ 48
    - (819200 : F) * a4 ^ 4 * b5 * h ^ 44
    - (3440640 : F) * a4 ^ 3 * a3 ^ 2 * lambda * h ^ 47
    + (22937600 : F) * a4 ^ 3 * a3 * a2 * h ^ 48
    - (3932160 : F) * a4 ^ 3 * a3 * b6 * h ^ 44
    - (4587520 : F) * a4 ^ 3 * a2 * b7 * h ^ 44
    - (5242880 : F) * a4 ^ 3 * a1 * b8 * h ^ 44
    + (1966080 : F) * a4 ^ 3 * a0 * lambda * h ^ 53
    + (786432 : F) * a4 ^ 3 * b3 * h ^ 50
    + (11468800 : F) * a4 ^ 2 * a3 ^ 3 * h ^ 48
    - (6881280 : F) * a4 ^ 2 * a3 ^ 2 * b7 * h ^ 44
    - (15728640 : F) * a4 ^ 2 * a3 * a2 * b8 * h ^ 44
    + (5898240 : F) * a4 ^ 2 * a3 * a1 * lambda * h ^ 53
    - (19660800 : F) * a4 ^ 2 * a3 * a0 * h ^ 54
    + (3145728 : F) * a4 ^ 2 * a3 * b4 * h ^ 50
    + (2949120 : F) * a4 ^ 2 * a2 ^ 2 * lambda * h ^ 53
    - (19660800 : F) * a4 ^ 2 * a2 * a1 * h ^ 54
    + (3932160 : F) * a4 ^ 2 * a2 * b5 * h ^ 50
    + (4718592 : F) * a4 ^ 2 * a1 * b6 * h ^ 50
    + (5505024 : F) * a4 ^ 2 * a0 * b7 * h ^ 50
    - (524288 : F) * a4 ^ 2 * b1 * h ^ 56
    - (5242880 : F) * a4 * a3 ^ 3 * b8 * h ^ 44
    + (5898240 : F) * a4 * a3 ^ 2 * a2 * lambda * h ^ 53
    - (19660800 : F) * a4 * a3 ^ 2 * a1 * h ^ 54
    + (3932160 : F) * a4 * a3 ^ 2 * b5 * h ^ 50
    - (19660800 : F) * a4 * a3 * a2 ^ 2 * h ^ 54
    + (9437184 : F) * a4 * a3 * a2 * b6 * h ^ 50
    + (11010048 : F) * a4 * a3 * a1 * b7 * h ^ 50
    + (12582912 : F) * a4 * a3 * a0 * b8 * h ^ 50
    - (2097152 : F) * a4 * a3 * b2 * h ^ 56
    + (5505024 : F) * a4 * a2 ^ 2 * b7 * h ^ 50
    + (12582912 : F) * a4 * a2 * a1 * b8 * h ^ 50
    - (4718592 : F) * a4 * a2 * a0 * lambda * h ^ 59
    - (3145728 : F) * a4 * a2 * b3 * h ^ 56
    - (2359296 : F) * a4 * a1 ^ 2 * lambda * h ^ 59
    + (15728640 : F) * a4 * a1 * a0 * h ^ 60
    - (4194304 : F) * a4 * a1 * b4 * h ^ 56
    - (5242880 : F) * a4 * a0 * b5 * h ^ 56
    + (491520 : F) * a3 ^ 4 * lambda * h ^ 53
    - (6553600 : F) * a3 ^ 3 * a2 * h ^ 54
    + (1572864 : F) * a3 ^ 3 * b6 * h ^ 50
    + (5505024 : F) * a3 ^ 2 * a2 * b7 * h ^ 50
    + (6291456 : F) * a3 ^ 2 * a1 * b8 * h ^ 50
    - (2359296 : F) * a3 ^ 2 * a0 * lambda * h ^ 59
    - (1572864 : F) * a3 ^ 2 * b3 * h ^ 56
    + (6291456 : F) * a3 * a2 ^ 2 * b8 * h ^ 50
    - (4718592 : F) * a3 * a2 * a1 * lambda * h ^ 59
    + (15728640 : F) * a3 * a2 * a0 * h ^ 60
    - (4194304 : F) * a3 * a2 * b4 * h ^ 56
    + (7864320 : F) * a3 * a1 ^ 2 * h ^ 60
    - (5242880 : F) * a3 * a1 * b5 * h ^ 56
    - (6291456 : F) * a3 * a0 * b6 * h ^ 56
    - (786432 : F) * a2 ^ 3 * lambda * h ^ 59
    + (7864320 : F) * a2 ^ 2 * a1 * h ^ 60
    - (2621440 : F) * a2 ^ 2 * b5 * h ^ 56
    - (6291456 : F) * a2 * a1 * b6 * h ^ 56
    - (7340032 : F) * a2 * a0 * b7 * h ^ 56
    + (2097152 : F) * a2 * b1 * h ^ 62
    - (3670016 : F) * a1 ^ 2 * b7 * h ^ 56
    - (8388608 : F) * a1 * a0 * b8 * h ^ 56
    + (4194304 : F) * a1 * b2 * h ^ 62
    + (1572864 : F) * a0 ^ 2 * lambda * h ^ 65
    + (6291456 : F) * a0 * b3 * h ^ 62 := by
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
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h108 : (108 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h162 : (162 : F) ≠ 0 := by norm_num
  have h576 : (576 : F) ≠ 0 := by norm_num
  have h972 : (972 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h1458 : (1458 : F) ≠ 0 := by norm_num
  have h3456 : (3456 : F) ≠ 0 := by norm_num
  have h15552 : (15552 : F) ≠ 0 := by norm_num
  have h12582912 : (12582912 : F) ≠ 0 := by norm_num
  have hh65 : h ^ 65 ≠ 0 := pow_ne_zero 65 hh
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
  simp only [bridgeMuResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hW, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h32,
    h36, h54, h64, h72, h81, h144, h216, h243, h256, h324, h432, h648,
    h729, h1296, h6561, h7776, h11664, h31104, h46656, h93312, h186624,
    h5038848, h258280326, h24, h108, h128, h162, h576, h972, h1024, h1458,
    h3456, h15552, h12582912, hh10, hh15, hh20, hh25, hh30, hh35, hh40,
    hh45, hh50, hh55, hh60, hh65]
  ring

end BridgeMuDepression610

/-! ## Degree-`2` depressed differential row -/

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

/-! ## Weight-`65` power relation on the literal source -/

section BridgeMuPowerRelation610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The twelfth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁶⁵`.  The weight-fifty `ι`,
weight-fifty-five `κ` and weight-sixty `λ` residuals remain available
from the terminal, kappa and lambda bridge packets. -/
theorem nonzeroFace610_bridgeMuPowerRelation
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
      bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C nu * h0 ^ 65 := by
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
  have hrow4 :
      (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 0) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 1) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 2) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 3) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 3) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_4_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 4) hbracket
    simpa [f, g, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow2 :
      (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 0) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 1) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 2) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 2) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 1) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_2_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 2) hbracket
    simpa [f, g, Polynomial.coeff_C, show (2 : ℕ) ≠ 0 by norm_num] using
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
  have hmu0deriv :
      ratFuncDerivation68
        (bridgeMuResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    bridgeMuResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha0
      hbeta0 hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      htheta0deriv (by simpa using hrow6) (by simpa using hrow5)
      (by simpa using hrow4) (by simpa using hrow2)
  obtain ⟨nu0, hnu0⟩ :
      ∃ a : k,
        bridgeMuResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hmu0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (12582912 : RatFunc k) * hRF ^ 65 *
          bridgeMuResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := bridgeMuDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [bridgeClearedMuDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, b1, bridgeMuResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, zetaResidual610, etaResidual610,
      bridgeThetaResidual610, hf4, hf3, hf2, hf1, hf0, hg1, hg2, hg3, hg4, hg5,
      hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (12582912 * nu0) * h0 ^ 65) := by
    rw [hclear, hnu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨12582912 * nu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end BridgeMuPowerRelation610

/-! ## Jet heads and tails of the cleared `μ` defect -/

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

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `μ` defect above order `h⁶⁰`. -/
def bridgeMuJetTail610
    (hh w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lam : R) : R :=
    - (180880 : R) * w1 ^ 13 * hh ^ 5
    + (88179 : R) * w1 ^ 12 * lam * hh ^ 5
    + (2015520 : R) * w1 ^ 11 * a41 * hh ^ 4
    + (268736 : R) * w1 ^ 11 * s1 * hh ^ 4
    - (1108536 : R) * w1 ^ 10 * a41 * lam * hh ^ 4
    - (2139280 : R) * w1 ^ 10 * p32 * hh ^ 4
    - (272272 : R) * w1 ^ 10 * u2 * hh ^ 4
    - (7779200 : R) * w1 ^ 9 * a41 ^ 2 * hh ^ 3
    - (3111680 : R) * w1 ^ 9 * a41 * s1 * hh ^ 3
    + (1166880 : R) * w1 ^ 9 * p32 * lam * hh ^ 4
    + (274560 : R) * w1 ^ 9 * b62 * hh ^ 3
    + (2288000 : R) * w1 ^ 9 * p2 * hh ^ 3
    + (5250960 : R) * w1 ^ 8 * a41 ^ 2 * lam * hh ^ 3
    + (14414400 : R) * w1 ^ 8 * a41 * p32 * hh ^ 3
    + (2882880 : R) * w1 ^ 8 * a41 * u2 * hh ^ 3
    + (3294720 : R) * w1 ^ 8 * p32 * s1 * hh ^ 3
    - (274560 : R) * w1 ^ 8 * q53 * hh ^ 3
    - (1235520 : R) * w1 ^ 8 * p2 * lam * hh ^ 3
    - (2471040 : R) * w1 ^ 8 * p1 * hh ^ 4
    + (10982400 : R) * w1 ^ 7 * a41 ^ 3 * hh ^ 2
    + (13178880 : R) * w1 ^ 7 * a41 ^ 2 * s1 * hh ^ 2
    - (9884160 : R) * w1 ^ 7 * a41 * p32 * lam * hh ^ 3
    - (2635776 : R) * w1 ^ 7 * a41 * b62 * hh ^ 2
    - (13178880 : R) * w1 ^ 7 * a41 * p2 * hh ^ 2
    - (6589440 : R) * w1 ^ 7 * p32 ^ 2 * hh ^ 3
    - (3075072 : R) * w1 ^ 7 * p32 * u2 * hh ^ 3
    - (3514368 : R) * w1 ^ 7 * s1 * p2 * hh ^ 2
    + (1317888 : R) * w1 ^ 7 * p1 * lam * hh ^ 4
    + (2703360 : R) * w1 ^ 7 * p0 * hh ^ 5
    + (270336 : R) * w1 ^ 7 * q41 * hh ^ 2
    - (11531520 : R) * w1 ^ 6 * a41 ^ 3 * lam * hh ^ 2
    - (23063040 : R) * w1 ^ 6 * a41 ^ 2 * p32 * hh ^ 2
    - (10762752 : R) * w1 ^ 6 * a41 ^ 2 * u2 * hh ^ 2
    - (24600576 : R) * w1 ^ 6 * a41 * p32 * s1 * hh ^ 2
    + (2365440 : R) * w1 ^ 6 * a41 * q53 * hh ^ 2
    + (9225216 : R) * w1 ^ 6 * a41 * p2 * lam * hh ^ 2
    + (11827200 : R) * w1 ^ 6 * a41 * p1 * hh ^ 3
    + (4612608 : R) * w1 ^ 6 * p32 ^ 2 * lam * hh ^ 3
    + (2838528 : R) * w1 ^ 6 * p32 * b62 * hh ^ 2
    + (11827200 : R) * w1 ^ 6 * p32 * p2 * hh ^ 2
    + (3784704 : R) * w1 ^ 6 * s1 * p1 * hh ^ 3
    + (3311616 : R) * w1 ^ 6 * u2 * p2 * hh ^ 2
    - (1419264 : R) * w1 ^ 6 * p0 * lam * hh ^ 5
    - (258048 : R) * w1 ^ 6 * q3 * hh ^ 2
    - (24600576 : R) * w1 ^ 5 * a41 ^ 3 * s1 * hh
    + (27675648 : R) * w1 ^ 5 * a41 ^ 2 * p32 * lam * hh ^ 2
    + (8515584 : R) * w1 ^ 5 * a41 ^ 2 * b62 * hh
    + (14192640 : R) * w1 ^ 5 * a41 ^ 2 * p2 * hh
    + (14192640 : R) * w1 ^ 5 * a41 * p32 ^ 2 * hh ^ 2
    + (19869696 : R) * w1 ^ 5 * a41 * p32 * u2 * hh ^ 2
    + (22708224 : R) * w1 ^ 5 * a41 * s1 * p2 * hh
    - (8515584 : R) * w1 ^ 5 * a41 * p1 * lam * hh ^ 3
    - (10321920 : R) * w1 ^ 5 * a41 * p0 * hh ^ 4
    - (2064384 : R) * w1 ^ 5 * a41 * q41 * hh
    + (11354112 : R) * w1 ^ 5 * p32 ^ 2 * s1 * hh ^ 2
    - (2580480 : R) * w1 ^ 5 * p32 * q53 * hh ^ 2
    - (8515584 : R) * w1 ^ 5 * p32 * p2 * lam * hh ^ 2
    - (10321920 : R) * w1 ^ 5 * p32 * p1 * hh ^ 3
    - (4128768 : R) * w1 ^ 5 * s1 * p0 * hh ^ 4
    - (3612672 : R) * w1 ^ 5 * u2 * p1 * hh ^ 3
    - (3096576 : R) * w1 ^ 5 * b62 * p2 * hh
    - (5160960 : R) * w1 ^ 5 * p2 ^ 2 * hh
    + (229376 : R) * w1 ^ 5 * q2 * hh ^ 3
    + (11531520 : R) * w1 ^ 4 * a41 ^ 4 * lam * hh
    - (11827200 : R) * w1 ^ 4 * a41 ^ 3 * p32 * hh
    + (16558080 : R) * w1 ^ 4 * a41 ^ 3 * u2 * hh
    + (56770560 : R) * w1 ^ 4 * a41 ^ 2 * p32 * s1 * hh
    - (6451200 : R) * w1 ^ 4 * a41 ^ 2 * q53 * hh
    - (21288960 : R) * w1 ^ 4 * a41 ^ 2 * p2 * lam * hh
    - (6451200 : R) * w1 ^ 4 * a41 ^ 2 * p1 * hh ^ 2
    - (21288960 : R) * w1 ^ 4 * a41 * p32 ^ 2 * lam * hh ^ 2
    - (15482880 : R) * w1 ^ 4 * a41 * p32 * b62 * hh
    - (12902400 : R) * w1 ^ 4 * a41 * p32 * p2 * hh
    - (20643840 : R) * w1 ^ 4 * a41 * s1 * p1 * hh ^ 2
    - (18063360 : R) * w1 ^ 4 * a41 * u2 * p2 * hh
    + (7741440 : R) * w1 ^ 4 * a41 * p0 * lam * hh ^ 4
    + (1720320 : R) * w1 ^ 4 * a41 * q3 * hh
    - (2150400 : R) * w1 ^ 4 * p32 ^ 3 * hh ^ 2
    - (9031680 : R) * w1 ^ 4 * p32 ^ 2 * u2 * hh ^ 2
    - (20643840 : R) * w1 ^ 4 * p32 * s1 * p2 * hh
    + (7741440 : R) * w1 ^ 4 * p32 * p1 * lam * hh ^ 3
    + (8601600 : R) * w1 ^ 4 * p32 * p0 * hh ^ 4
    + (2293760 : R) * w1 ^ 4 * p32 * q41 * hh
    + (4014080 : R) * w1 ^ 4 * u2 * p0 * hh ^ 4
    + (3440640 : R) * w1 ^ 4 * b62 * p1 * hh ^ 2
    + (2867200 : R) * w1 ^ 4 * q53 * p2 * hh
    + (3870720 : R) * w1 ^ 4 * p2 ^ 2 * lam * hh
    + (8601600 : R) * w1 ^ 4 * p2 * p1 * hh ^ 2
    - (163840 : R) * w1 ^ 4 * q1 * hh ^ 4
    - (9461760 : R) * w1 ^ 3 * a41 ^ 5
    + (18923520 : R) * w1 ^ 3 * a41 ^ 4 * s1
    - (28385280 : R) * w1 ^ 3 * a41 ^ 3 * p32 * lam * hh
    - (10321920 : R) * w1 ^ 3 * a41 ^ 3 * b62
    + (17203200 : R) * w1 ^ 3 * a41 ^ 3 * p2
    + (25804800 : R) * w1 ^ 3 * a41 ^ 2 * p32 ^ 2 * hh
    - (36126720 : R) * w1 ^ 3 * a41 ^ 2 * p32 * u2 * hh
    - (41287680 : R) * w1 ^ 3 * a41 ^ 2 * s1 * p2
    + (15482880 : R) * w1 ^ 3 * a41 ^ 2 * p1 * lam * hh ^ 2
    + (4587520 : R) * w1 ^ 3 * a41 ^ 2 * q41
    - (41287680 : R) * w1 ^ 3 * a41 * p32 ^ 2 * s1 * hh
    + (11468800 : R) * w1 ^ 3 * a41 * p32 * q53 * hh
    + (30965760 : R) * w1 ^ 3 * a41 * p32 * p2 * lam * hh
    + (18350080 : R) * w1 ^ 3 * a41 * s1 * p0 * hh ^ 3
    + (16056320 : R) * w1 ^ 3 * a41 * u2 * p1 * hh ^ 2
    + (13762560 : R) * w1 ^ 3 * a41 * b62 * p2
    - (1310720 : R) * w1 ^ 3 * a41 * q2 * hh ^ 2
    + (5160960 : R) * w1 ^ 3 * p32 ^ 3 * lam * hh ^ 2
    + (6881280 : R) * w1 ^ 3 * p32 ^ 2 * b62 * hh
    + (18350080 : R) * w1 ^ 3 * p32 * s1 * p1 * hh ^ 2
    + (16056320 : R) * w1 ^ 3 * p32 * u2 * p2 * hh
    - (6881280 : R) * w1 ^ 3 * p32 * p0 * lam * hh ^ 4
    - (1966080 : R) * w1 ^ 3 * p32 * q3 * hh
    + (9175040 : R) * w1 ^ 3 * s1 * p2 ^ 2
    - (3932160 : R) * w1 ^ 3 * b62 * p0 * hh ^ 3
    - (3276800 : R) * w1 ^ 3 * q53 * p1 * hh ^ 2
    - (6881280 : R) * w1 ^ 3 * p2 * p1 * lam * hh ^ 2
    - (6553600 : R) * w1 ^ 3 * p2 * p0 * hh ^ 3
    - (2621440 : R) * w1 ^ 3 * p2 * q41
    - (3276800 : R) * w1 ^ 3 * p1 ^ 2 * hh ^ 3
    - (4257792 : R) * w1 ^ 2 * a41 ^ 5 * lam
    + (32256000 : R) * w1 ^ 2 * a41 ^ 4 * p32
    - (9031680 : R) * w1 ^ 2 * a41 ^ 4 * u2
    - (41287680 : R) * w1 ^ 2 * a41 ^ 3 * p32 * s1
    + (5734400 : R) * w1 ^ 2 * a41 ^ 3 * q53
    + (15482880 : R) * w1 ^ 2 * a41 ^ 3 * p2 * lam
    - (17203200 : R) * w1 ^ 2 * a41 ^ 3 * p1 * hh
    + (23224320 : R) * w1 ^ 2 * a41 ^ 2 * p32 ^ 2 * lam * hh
    + (20643840 : R) * w1 ^ 2 * a41 ^ 2 * p32 * b62
    - (51609600 : R) * w1 ^ 2 * a41 ^ 2 * p32 * p2
    + (27525120 : R) * w1 ^ 2 * a41 ^ 2 * s1 * p1 * hh
    + (24084480 : R) * w1 ^ 2 * a41 ^ 2 * u2 * p2
    - (10321920 : R) * w1 ^ 2 * a41 ^ 2 * p0 * lam * hh ^ 3
    - (2949120 : R) * w1 ^ 2 * a41 ^ 2 * q3
    - (17203200 : R) * w1 ^ 2 * a41 * p32 ^ 3 * hh
    + (24084480 : R) * w1 ^ 2 * a41 * p32 ^ 2 * u2 * hh
    + (55050240 : R) * w1 ^ 2 * a41 * p32 * s1 * p2
    - (20643840 : R) * w1 ^ 2 * a41 * p32 * p1 * lam * hh ^ 2
    + (9830400 : R) * w1 ^ 2 * a41 * p32 * p0 * hh ^ 3
    - (7864320 : R) * w1 ^ 2 * a41 * p32 * q41
    - (13762560 : R) * w1 ^ 2 * a41 * u2 * p0 * hh ^ 3
    - (11796480 : R) * w1 ^ 2 * a41 * b62 * p1 * hh
    - (9830400 : R) * w1 ^ 2 * a41 * q53 * p2
    - (10321920 : R) * w1 ^ 2 * a41 * p2 ^ 2 * lam
    + (9830400 : R) * w1 ^ 2 * a41 * p2 * p1 * hh
    + (786432 : R) * w1 ^ 2 * a41 * q1 * hh ^ 3
    + (9175040 : R) * w1 ^ 2 * p32 ^ 3 * s1 * hh
    - (4915200 : R) * w1 ^ 2 * p32 ^ 2 * q53 * hh
    - (10321920 : R) * w1 ^ 2 * p32 ^ 2 * p2 * lam * hh
    + (4915200 : R) * w1 ^ 2 * p32 ^ 2 * p1 * hh ^ 2
    - (15728640 : R) * w1 ^ 2 * p32 * s1 * p0 * hh ^ 3
    - (13762560 : R) * w1 ^ 2 * p32 * u2 * p1 * hh ^ 2
    - (11796480 : R) * w1 ^ 2 * p32 * b62 * p2
    + (4915200 : R) * w1 ^ 2 * p32 * p2 ^ 2
    + (1572864 : R) * w1 ^ 2 * p32 * q2 * hh ^ 2
    - (15728640 : R) * w1 ^ 2 * s1 * p2 * p1 * hh
    - (6881280 : R) * w1 ^ 2 * u2 * p2 ^ 2
    + (3932160 : R) * w1 ^ 2 * q53 * p0 * hh ^ 3
    + (5898240 : R) * w1 ^ 2 * p2 * p0 * lam * hh ^ 3
    + (2359296 : R) * w1 ^ 2 * p2 * q3
    + (2949120 : R) * w1 ^ 2 * p1 ^ 2 * lam * hh ^ 3
    + (3932160 : R) * w1 ^ 2 * p1 * p0 * hh ^ 4
    + (3145728 : R) * w1 ^ 2 * p1 * q41 * hh
    + (7741440 : R) * w1 * a41 ^ 4 * p32 * lam
    - (34406400 : R) * w1 * a41 ^ 3 * p32 ^ 2
    + (16056320 : R) * w1 * a41 ^ 3 * p32 * u2
    - (6881280 : R) * w1 * a41 ^ 3 * p1 * lam * hh
    + (13107200 : R) * w1 * a41 ^ 3 * p0 * hh ^ 2
    + (27525120 : R) * w1 * a41 ^ 2 * p32 ^ 2 * s1
    - (9830400 : R) * w1 * a41 ^ 2 * p32 * q53
    - (20643840 : R) * w1 * a41 ^ 2 * p32 * p2 * lam
    + (39321600 : R) * w1 * a41 ^ 2 * p32 * p1 * hh
    - (15728640 : R) * w1 * a41 ^ 2 * s1 * p0 * hh ^ 2
    - (13762560 : R) * w1 * a41 ^ 2 * u2 * p1 * hh
    + (1572864 : R) * w1 * a41 ^ 2 * q2 * hh
    - (6881280 : R) * w1 * a41 * p32 ^ 3 * lam * hh
    - (11796480 : R) * w1 * a41 * p32 ^ 2 * b62
    + (39321600 : R) * w1 * a41 * p32 ^ 2 * p2
    - (31457280 : R) * w1 * a41 * p32 * s1 * p1 * hh
    - (27525120 : R) * w1 * a41 * p32 * u2 * p2
    + (11796480 : R) * w1 * a41 * p32 * p0 * lam * hh ^ 3
    + (4718592 : R) * w1 * a41 * p32 * q3
    + (9437184 : R) * w1 * a41 * b62 * p0 * hh ^ 2
    + (7864320 : R) * w1 * a41 * q53 * p1 * hh
    + (11796480 : R) * w1 * a41 * p2 * p1 * lam * hh
    - (15728640 : R) * w1 * a41 * p2 * p0 * hh ^ 2
    - (7864320 : R) * w1 * a41 * p1 ^ 2 * hh ^ 2
    + (3276800 : R) * w1 * p32 ^ 4 * hh
    - (4587520 : R) * w1 * p32 ^ 3 * u2 * hh
    - (15728640 : R) * w1 * p32 ^ 2 * s1 * p2
    + (5898240 : R) * w1 * p32 ^ 2 * p1 * lam * hh ^ 2
    - (7864320 : R) * w1 * p32 ^ 2 * p0 * hh ^ 3
    + (3145728 : R) * w1 * p32 ^ 2 * q41
    + (11010048 : R) * w1 * p32 * u2 * p0 * hh ^ 3
    + (9437184 : R) * w1 * p32 * b62 * p1 * hh
    + (7864320 : R) * w1 * p32 * q53 * p2
    + (5898240 : R) * w1 * p32 * p2 ^ 2 * lam
    - (15728640 : R) * w1 * p32 * p2 * p1 * hh
    - (1048576 : R) * w1 * p32 * q1 * hh ^ 3
    + (12582912 : R) * w1 * s1 * p2 * p0 * hh ^ 2
    + (6291456 : R) * w1 * s1 * p1 ^ 2 * hh ^ 2
    + (11010048 : R) * w1 * u2 * p2 * p1 * hh
    - (2097152 : R) * w1 * p2 * q2 * hh
    - (4718592 : R) * w1 * p1 * p0 * lam * hh ^ 4
    - (3145728 : R) * w1 * p1 * q3 * hh
    - (4194304 : R) * w1 * p0 * q41 * hh ^ 2
    + (5734400 : R) * a41 ^ 4 * p1
    - (3440640 : R) * a41 ^ 3 * p32 ^ 2 * lam
    - (5242880 : R) * a41 ^ 3 * s1 * p1
    + (1966080 : R) * a41 ^ 3 * p0 * lam * hh ^ 2
    + (11468800 : R) * a41 ^ 2 * p32 ^ 3
    - (6881280 : R) * a41 ^ 2 * p32 ^ 2 * u2
    + (5898240 : R) * a41 ^ 2 * p32 * p1 * lam * hh
    - (19660800 : R) * a41 ^ 2 * p32 * p0 * hh ^ 2
    + (5505024 : R) * a41 ^ 2 * u2 * p0 * hh ^ 2
    + (4718592 : R) * a41 ^ 2 * b62 * p1
    - (19660800 : R) * a41 ^ 2 * p2 * p1
    - (524288 : R) * a41 ^ 2 * q1 * hh ^ 2
    - (5242880 : R) * a41 * p32 ^ 3 * s1
    + (3932160 : R) * a41 * p32 ^ 2 * q53
    + (5898240 : R) * a41 * p32 ^ 2 * p2 * lam
    - (19660800 : R) * a41 * p32 ^ 2 * p1 * hh
    + (12582912 : R) * a41 * p32 * s1 * p0 * hh ^ 2
    + (11010048 : R) * a41 * p32 * u2 * p1 * hh
    - (2097152 : R) * a41 * p32 * q2 * hh
    + (12582912 : R) * a41 * s1 * p2 * p1
    - (5242880 : R) * a41 * q53 * p0 * hh ^ 2
    - (4718592 : R) * a41 * p2 * p0 * lam * hh ^ 2
    - (2359296 : R) * a41 * p1 ^ 2 * lam * hh ^ 2
    + (15728640 : R) * a41 * p1 * p0 * hh ^ 3
    - (4194304 : R) * a41 * p1 * q41
    + (491520 : R) * p32 ^ 4 * lam * hh
    + (1572864 : R) * p32 ^ 3 * b62
    - (6553600 : R) * p32 ^ 3 * p2
    + (6291456 : R) * p32 ^ 2 * s1 * p1 * hh
    + (5505024 : R) * p32 ^ 2 * u2 * p2
    - (2359296 : R) * p32 ^ 2 * p0 * lam * hh ^ 3
    - (1572864 : R) * p32 ^ 2 * q3
    - (6291456 : R) * p32 * b62 * p0 * hh ^ 2
    - (5242880 : R) * p32 * q53 * p1 * hh
    - (4718592 : R) * p32 * p2 * p1 * lam * hh
    + (15728640 : R) * p32 * p2 * p0 * hh ^ 2
    + (7864320 : R) * p32 * p1 ^ 2 * hh ^ 2
    - (8388608 : R) * s1 * p1 * p0 * hh ^ 3
    - (7340032 : R) * u2 * p2 * p0 * hh ^ 2
    - (3670016 : R) * u2 * p1 ^ 2 * hh ^ 2
    - (6291456 : R) * b62 * p2 * p1
    + (7864320 : R) * p2 ^ 2 * p1
    + (2097152 : R) * p2 * q1 * hh ^ 2
    + (4194304 : R) * p1 * q2 * hh ^ 2
    + (1572864 : R) * p0 ^ 2 * lam * hh ^ 5
    + (6291456 : R) * p0 * q3 * hh ^ 2

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

set_option maxHeartbeats 40000000 in
/-- Tail of the sibling-child deep jet above order `h⁶²`. -/
def bridgeMuDeepTail610
    (hh w1 a42 p32 s2 u2 b63 q54 p21 p1 p0 q42 q31 q2 q1 lam : R) : R :=
    - (180880 : R) * w1 ^ 13 * hh ^ 3
    + (88179 : R) * w1 ^ 12 * lam * hh ^ 3
    + (2015520 : R) * w1 ^ 11 * a42 * hh ^ 3
    + (268736 : R) * w1 ^ 11 * s2 * hh ^ 3
    - (1108536 : R) * w1 ^ 10 * a42 * lam * hh ^ 3
    - (2139280 : R) * w1 ^ 10 * p32 * hh ^ 2
    - (272272 : R) * w1 ^ 10 * u2 * hh ^ 2
    - (7779200 : R) * w1 ^ 9 * a42 ^ 2 * hh ^ 3
    - (3111680 : R) * w1 ^ 9 * a42 * s2 * hh ^ 3
    + (1166880 : R) * w1 ^ 9 * p32 * lam * hh ^ 2
    + (274560 : R) * w1 ^ 9 * b63 * hh ^ 2
    + (2288000 : R) * w1 ^ 9 * p21 * hh ^ 2
    + (5250960 : R) * w1 ^ 8 * a42 ^ 2 * lam * hh ^ 3
    + (14414400 : R) * w1 ^ 8 * a42 * p32 * hh ^ 2
    + (2882880 : R) * w1 ^ 8 * a42 * u2 * hh ^ 2
    + (3294720 : R) * w1 ^ 8 * p32 * s2 * hh ^ 2
    - (274560 : R) * w1 ^ 8 * q54 * hh ^ 2
    - (1235520 : R) * w1 ^ 8 * p21 * lam * hh ^ 2
    - (2471040 : R) * w1 ^ 8 * p1 * hh ^ 2
    + (10982400 : R) * w1 ^ 7 * a42 ^ 3 * hh ^ 3
    + (13178880 : R) * w1 ^ 7 * a42 ^ 2 * s2 * hh ^ 3
    - (9884160 : R) * w1 ^ 7 * a42 * p32 * lam * hh ^ 2
    - (2635776 : R) * w1 ^ 7 * a42 * b63 * hh ^ 2
    - (13178880 : R) * w1 ^ 7 * a42 * p21 * hh ^ 2
    - (6589440 : R) * w1 ^ 7 * p32 ^ 2 * hh
    - (3075072 : R) * w1 ^ 7 * p32 * u2 * hh
    - (3514368 : R) * w1 ^ 7 * s2 * p21 * hh ^ 2
    + (1317888 : R) * w1 ^ 7 * p1 * lam * hh ^ 2
    + (2703360 : R) * w1 ^ 7 * p0 * hh ^ 3
    + (270336 : R) * w1 ^ 7 * q42 * hh
    - (11531520 : R) * w1 ^ 6 * a42 ^ 3 * lam * hh ^ 3
    - (23063040 : R) * w1 ^ 6 * a42 ^ 2 * p32 * hh ^ 2
    - (10762752 : R) * w1 ^ 6 * a42 ^ 2 * u2 * hh ^ 2
    - (24600576 : R) * w1 ^ 6 * a42 * p32 * s2 * hh ^ 2
    + (2365440 : R) * w1 ^ 6 * a42 * q54 * hh ^ 2
    + (9225216 : R) * w1 ^ 6 * a42 * p21 * lam * hh ^ 2
    + (11827200 : R) * w1 ^ 6 * a42 * p1 * hh ^ 2
    + (4612608 : R) * w1 ^ 6 * p32 ^ 2 * lam * hh
    + (2838528 : R) * w1 ^ 6 * p32 * b63 * hh
    + (11827200 : R) * w1 ^ 6 * p32 * p21 * hh
    + (3784704 : R) * w1 ^ 6 * s2 * p1 * hh ^ 2
    + (3311616 : R) * w1 ^ 6 * u2 * p21 * hh
    - (1419264 : R) * w1 ^ 6 * p0 * lam * hh ^ 3
    - (258048 : R) * w1 ^ 6 * q31 * hh
    - (24600576 : R) * w1 ^ 5 * a42 ^ 3 * s2 * hh ^ 3
    + (27675648 : R) * w1 ^ 5 * a42 ^ 2 * p32 * lam * hh ^ 2
    + (8515584 : R) * w1 ^ 5 * a42 ^ 2 * b63 * hh ^ 2
    + (14192640 : R) * w1 ^ 5 * a42 ^ 2 * p21 * hh ^ 2
    + (14192640 : R) * w1 ^ 5 * a42 * p32 ^ 2 * hh
    + (19869696 : R) * w1 ^ 5 * a42 * p32 * u2 * hh
    + (22708224 : R) * w1 ^ 5 * a42 * s2 * p21 * hh ^ 2
    - (8515584 : R) * w1 ^ 5 * a42 * p1 * lam * hh ^ 2
    - (10321920 : R) * w1 ^ 5 * a42 * p0 * hh ^ 3
    - (2064384 : R) * w1 ^ 5 * a42 * q42 * hh
    + (11354112 : R) * w1 ^ 5 * p32 ^ 2 * s2 * hh
    - (2580480 : R) * w1 ^ 5 * p32 * q54 * hh
    - (8515584 : R) * w1 ^ 5 * p32 * p21 * lam * hh
    - (10321920 : R) * w1 ^ 5 * p32 * p1 * hh
    - (4128768 : R) * w1 ^ 5 * s2 * p0 * hh ^ 3
    - (3612672 : R) * w1 ^ 5 * u2 * p1 * hh
    - (3096576 : R) * w1 ^ 5 * b63 * p21 * hh
    - (5160960 : R) * w1 ^ 5 * p21 ^ 2 * hh
    + (229376 : R) * w1 ^ 5 * q2 * hh
    + (11531520 : R) * w1 ^ 4 * a42 ^ 4 * lam * hh ^ 3
    - (11827200 : R) * w1 ^ 4 * a42 ^ 3 * p32 * hh ^ 2
    + (16558080 : R) * w1 ^ 4 * a42 ^ 3 * u2 * hh ^ 2
    + (56770560 : R) * w1 ^ 4 * a42 ^ 2 * p32 * s2 * hh ^ 2
    - (6451200 : R) * w1 ^ 4 * a42 ^ 2 * q54 * hh ^ 2
    - (21288960 : R) * w1 ^ 4 * a42 ^ 2 * p21 * lam * hh ^ 2
    - (6451200 : R) * w1 ^ 4 * a42 ^ 2 * p1 * hh ^ 2
    - (21288960 : R) * w1 ^ 4 * a42 * p32 ^ 2 * lam * hh
    - (15482880 : R) * w1 ^ 4 * a42 * p32 * b63 * hh
    - (12902400 : R) * w1 ^ 4 * a42 * p32 * p21 * hh
    - (20643840 : R) * w1 ^ 4 * a42 * s2 * p1 * hh ^ 2
    - (18063360 : R) * w1 ^ 4 * a42 * u2 * p21 * hh
    + (7741440 : R) * w1 ^ 4 * a42 * p0 * lam * hh ^ 3
    + (1720320 : R) * w1 ^ 4 * a42 * q31 * hh
    - (2150400 : R) * w1 ^ 4 * p32 ^ 3
    - (9031680 : R) * w1 ^ 4 * p32 ^ 2 * u2
    - (20643840 : R) * w1 ^ 4 * p32 * s2 * p21 * hh
    + (7741440 : R) * w1 ^ 4 * p32 * p1 * lam * hh
    + (8601600 : R) * w1 ^ 4 * p32 * p0 * hh ^ 2
    + (2293760 : R) * w1 ^ 4 * p32 * q42
    + (4014080 : R) * w1 ^ 4 * u2 * p0 * hh ^ 2
    + (3440640 : R) * w1 ^ 4 * b63 * p1 * hh
    + (2867200 : R) * w1 ^ 4 * q54 * p21 * hh
    + (3870720 : R) * w1 ^ 4 * p21 ^ 2 * lam * hh
    + (8601600 : R) * w1 ^ 4 * p21 * p1 * hh
    - (163840 : R) * w1 ^ 4 * q1 * hh ^ 2
    - (9461760 : R) * w1 ^ 3 * a42 ^ 5 * hh ^ 3
    + (18923520 : R) * w1 ^ 3 * a42 ^ 4 * s2 * hh ^ 3
    - (28385280 : R) * w1 ^ 3 * a42 ^ 3 * p32 * lam * hh ^ 2
    - (10321920 : R) * w1 ^ 3 * a42 ^ 3 * b63 * hh ^ 2
    + (17203200 : R) * w1 ^ 3 * a42 ^ 3 * p21 * hh ^ 2
    + (25804800 : R) * w1 ^ 3 * a42 ^ 2 * p32 ^ 2 * hh
    - (36126720 : R) * w1 ^ 3 * a42 ^ 2 * p32 * u2 * hh
    - (41287680 : R) * w1 ^ 3 * a42 ^ 2 * s2 * p21 * hh ^ 2
    + (15482880 : R) * w1 ^ 3 * a42 ^ 2 * p1 * lam * hh ^ 2
    + (4587520 : R) * w1 ^ 3 * a42 ^ 2 * q42 * hh
    - (41287680 : R) * w1 ^ 3 * a42 * p32 ^ 2 * s2 * hh
    + (11468800 : R) * w1 ^ 3 * a42 * p32 * q54 * hh
    + (30965760 : R) * w1 ^ 3 * a42 * p32 * p21 * lam * hh
    + (18350080 : R) * w1 ^ 3 * a42 * s2 * p0 * hh ^ 3
    + (16056320 : R) * w1 ^ 3 * a42 * u2 * p1 * hh
    + (13762560 : R) * w1 ^ 3 * a42 * b63 * p21 * hh
    - (1310720 : R) * w1 ^ 3 * a42 * q2 * hh
    + (5160960 : R) * w1 ^ 3 * p32 ^ 3 * lam
    + (6881280 : R) * w1 ^ 3 * p32 ^ 2 * b63
    + (18350080 : R) * w1 ^ 3 * p32 * s2 * p1 * hh
    + (16056320 : R) * w1 ^ 3 * p32 * u2 * p21
    - (6881280 : R) * w1 ^ 3 * p32 * p0 * lam * hh ^ 2
    - (1966080 : R) * w1 ^ 3 * p32 * q31
    + (9175040 : R) * w1 ^ 3 * s2 * p21 ^ 2 * hh
    - (3932160 : R) * w1 ^ 3 * b63 * p0 * hh ^ 2
    - (3276800 : R) * w1 ^ 3 * q54 * p1 * hh
    - (6881280 : R) * w1 ^ 3 * p21 * p1 * lam * hh
    - (6553600 : R) * w1 ^ 3 * p21 * p0 * hh ^ 2
    - (2621440 : R) * w1 ^ 3 * p21 * q42
    - (3276800 : R) * w1 ^ 3 * p1 ^ 2 * hh
    - (4257792 : R) * w1 ^ 2 * a42 ^ 5 * lam * hh ^ 3
    + (32256000 : R) * w1 ^ 2 * a42 ^ 4 * p32 * hh ^ 2
    - (9031680 : R) * w1 ^ 2 * a42 ^ 4 * u2 * hh ^ 2
    - (41287680 : R) * w1 ^ 2 * a42 ^ 3 * p32 * s2 * hh ^ 2
    + (5734400 : R) * w1 ^ 2 * a42 ^ 3 * q54 * hh ^ 2
    + (15482880 : R) * w1 ^ 2 * a42 ^ 3 * p21 * lam * hh ^ 2
    - (17203200 : R) * w1 ^ 2 * a42 ^ 3 * p1 * hh ^ 2
    + (23224320 : R) * w1 ^ 2 * a42 ^ 2 * p32 ^ 2 * lam * hh
    + (20643840 : R) * w1 ^ 2 * a42 ^ 2 * p32 * b63 * hh
    - (51609600 : R) * w1 ^ 2 * a42 ^ 2 * p32 * p21 * hh
    + (27525120 : R) * w1 ^ 2 * a42 ^ 2 * s2 * p1 * hh ^ 2
    + (24084480 : R) * w1 ^ 2 * a42 ^ 2 * u2 * p21 * hh
    - (10321920 : R) * w1 ^ 2 * a42 ^ 2 * p0 * lam * hh ^ 3
    - (2949120 : R) * w1 ^ 2 * a42 ^ 2 * q31 * hh
    - (17203200 : R) * w1 ^ 2 * a42 * p32 ^ 3
    + (24084480 : R) * w1 ^ 2 * a42 * p32 ^ 2 * u2
    + (55050240 : R) * w1 ^ 2 * a42 * p32 * s2 * p21 * hh
    - (20643840 : R) * w1 ^ 2 * a42 * p32 * p1 * lam * hh
    + (9830400 : R) * w1 ^ 2 * a42 * p32 * p0 * hh ^ 2
    - (7864320 : R) * w1 ^ 2 * a42 * p32 * q42
    - (13762560 : R) * w1 ^ 2 * a42 * u2 * p0 * hh ^ 2
    - (11796480 : R) * w1 ^ 2 * a42 * b63 * p1 * hh
    - (9830400 : R) * w1 ^ 2 * a42 * q54 * p21 * hh
    - (10321920 : R) * w1 ^ 2 * a42 * p21 ^ 2 * lam * hh
    + (9830400 : R) * w1 ^ 2 * a42 * p21 * p1 * hh
    + (786432 : R) * w1 ^ 2 * a42 * q1 * hh ^ 2
    + (9175040 : R) * w1 ^ 2 * p32 ^ 3 * s2
    - (4915200 : R) * w1 ^ 2 * p32 ^ 2 * q54
    - (10321920 : R) * w1 ^ 2 * p32 ^ 2 * p21 * lam
    + (4915200 : R) * w1 ^ 2 * p32 ^ 2 * p1
    - (15728640 : R) * w1 ^ 2 * p32 * s2 * p0 * hh ^ 2
    - (13762560 : R) * w1 ^ 2 * p32 * u2 * p1
    - (11796480 : R) * w1 ^ 2 * p32 * b63 * p21
    + (4915200 : R) * w1 ^ 2 * p32 * p21 ^ 2
    + (1572864 : R) * w1 ^ 2 * p32 * q2
    - (15728640 : R) * w1 ^ 2 * s2 * p21 * p1 * hh
    - (6881280 : R) * w1 ^ 2 * u2 * p21 ^ 2
    + (3932160 : R) * w1 ^ 2 * q54 * p0 * hh ^ 2
    + (5898240 : R) * w1 ^ 2 * p21 * p0 * lam * hh ^ 2
    + (2359296 : R) * w1 ^ 2 * p21 * q31
    + (2949120 : R) * w1 ^ 2 * p1 ^ 2 * lam * hh
    + (3932160 : R) * w1 ^ 2 * p1 * p0 * hh ^ 2
    + (3145728 : R) * w1 ^ 2 * p1 * q42
    + (3440640 : R) * w1 * a42 ^ 6 * hh ^ 3
    - (4128768 : R) * w1 * a42 ^ 5 * s2 * hh ^ 3
    + (7741440 : R) * w1 * a42 ^ 4 * p32 * lam * hh ^ 2
    + (3440640 : R) * w1 * a42 ^ 4 * b63 * hh ^ 2
    - (17203200 : R) * w1 * a42 ^ 4 * p21 * hh ^ 2
    - (34406400 : R) * w1 * a42 ^ 3 * p32 ^ 2 * hh
    + (16056320 : R) * w1 * a42 ^ 3 * p32 * u2 * hh
    + (18350080 : R) * w1 * a42 ^ 3 * s2 * p21 * hh ^ 2
    - (6881280 : R) * w1 * a42 ^ 3 * p1 * lam * hh ^ 2
    + (13107200 : R) * w1 * a42 ^ 3 * p0 * hh ^ 3
    - (2621440 : R) * w1 * a42 ^ 3 * q42 * hh
    + (27525120 : R) * w1 * a42 ^ 2 * p32 ^ 2 * s2 * hh
    - (9830400 : R) * w1 * a42 ^ 2 * p32 * q54 * hh
    - (20643840 : R) * w1 * a42 ^ 2 * p32 * p21 * lam * hh
    + (39321600 : R) * w1 * a42 ^ 2 * p32 * p1 * hh
    - (15728640 : R) * w1 * a42 ^ 2 * s2 * p0 * hh ^ 3
    - (13762560 : R) * w1 * a42 ^ 2 * u2 * p1 * hh
    - (11796480 : R) * w1 * a42 ^ 2 * b63 * p21 * hh
    + (19660800 : R) * w1 * a42 ^ 2 * p21 ^ 2 * hh
    + (1572864 : R) * w1 * a42 ^ 2 * q2 * hh
    - (6881280 : R) * w1 * a42 * p32 ^ 3 * lam
    - (11796480 : R) * w1 * a42 * p32 ^ 2 * b63
    + (39321600 : R) * w1 * a42 * p32 ^ 2 * p21
    - (31457280 : R) * w1 * a42 * p32 * s2 * p1 * hh
    - (27525120 : R) * w1 * a42 * p32 * u2 * p21
    + (11796480 : R) * w1 * a42 * p32 * p0 * lam * hh ^ 2
    + (4718592 : R) * w1 * a42 * p32 * q31
    - (15728640 : R) * w1 * a42 * s2 * p21 ^ 2 * hh
    + (9437184 : R) * w1 * a42 * b63 * p0 * hh ^ 2
    + (7864320 : R) * w1 * a42 * q54 * p1 * hh
    + (11796480 : R) * w1 * a42 * p21 * p1 * lam * hh
    - (15728640 : R) * w1 * a42 * p21 * p0 * hh ^ 2
    + (6291456 : R) * w1 * a42 * p21 * q42
    - (7864320 : R) * w1 * a42 * p1 ^ 2 * hh
    - (15728640 : R) * w1 * p32 ^ 2 * s2 * p21
    + (5898240 : R) * w1 * p32 ^ 2 * p1 * lam
    - (7864320 : R) * w1 * p32 ^ 2 * p0 * hh
    + (11010048 : R) * w1 * p32 * u2 * p0 * hh
    + (9437184 : R) * w1 * p32 * b63 * p1
    + (7864320 : R) * w1 * p32 * q54 * p21
    + (5898240 : R) * w1 * p32 * p21 ^ 2 * lam
    - (15728640 : R) * w1 * p32 * p21 * p1
    - (1048576 : R) * w1 * p32 * q1 * hh
    + (12582912 : R) * w1 * s2 * p21 * p0 * hh ^ 2
    + (6291456 : R) * w1 * s2 * p1 ^ 2 * hh
    + (11010048 : R) * w1 * u2 * p21 * p1
    + (4718592 : R) * w1 * b63 * p21 ^ 2
    - (2621440 : R) * w1 * p21 ^ 3
    - (2097152 : R) * w1 * p21 * q2
    - (4718592 : R) * w1 * p1 * p0 * lam * hh ^ 2
    - (3145728 : R) * w1 * p1 * q31
    - (4194304 : R) * w1 * p0 * q42 * hh
    + (258048 : R) * a42 ^ 6 * lam * hh ^ 3
    - (5160960 : R) * a42 ^ 5 * p32 * hh ^ 2
    + (802816 : R) * a42 ^ 5 * u2 * hh ^ 2
    + (4587520 : R) * a42 ^ 4 * p32 * s2 * hh ^ 2
    - (819200 : R) * a42 ^ 4 * q54 * hh ^ 2
    - (1720320 : R) * a42 ^ 4 * p21 * lam * hh ^ 2
    + (5734400 : R) * a42 ^ 4 * p1 * hh ^ 2
    - (3440640 : R) * a42 ^ 3 * p32 ^ 2 * lam * hh
    - (3932160 : R) * a42 ^ 3 * p32 * b63 * hh
    + (22937600 : R) * a42 ^ 3 * p32 * p21 * hh
    - (5242880 : R) * a42 ^ 3 * s2 * p1 * hh ^ 2
    - (4587520 : R) * a42 ^ 3 * u2 * p21 * hh
    + (1966080 : R) * a42 ^ 3 * p0 * lam * hh ^ 3
    + (786432 : R) * a42 ^ 3 * q31 * hh
    + (11468800 : R) * a42 ^ 2 * p32 ^ 3
    - (6881280 : R) * a42 ^ 2 * p32 ^ 2 * u2
    - (15728640 : R) * a42 ^ 2 * p32 * s2 * p21 * hh
    + (5898240 : R) * a42 ^ 2 * p32 * p1 * lam * hh
    - (19660800 : R) * a42 ^ 2 * p32 * p0 * hh ^ 2
    + (3145728 : R) * a42 ^ 2 * p32 * q42
    + (5505024 : R) * a42 ^ 2 * u2 * p0 * hh ^ 2
    + (4718592 : R) * a42 ^ 2 * b63 * p1 * hh
    + (3932160 : R) * a42 ^ 2 * q54 * p21 * hh
    + (2949120 : R) * a42 ^ 2 * p21 ^ 2 * lam * hh
    - (19660800 : R) * a42 ^ 2 * p21 * p1 * hh
    - (524288 : R) * a42 ^ 2 * q1 * hh ^ 2
    - (5242880 : R) * a42 * p32 ^ 3 * s2
    + (3932160 : R) * a42 * p32 ^ 2 * q54
    + (5898240 : R) * a42 * p32 ^ 2 * p21 * lam
    - (19660800 : R) * a42 * p32 ^ 2 * p1
    + (12582912 : R) * a42 * p32 * s2 * p0 * hh ^ 2
    + (11010048 : R) * a42 * p32 * u2 * p1
    + (9437184 : R) * a42 * p32 * b63 * p21
    - (19660800 : R) * a42 * p32 * p21 ^ 2
    - (2097152 : R) * a42 * p32 * q2
    + (12582912 : R) * a42 * s2 * p21 * p1 * hh
    + (5505024 : R) * a42 * u2 * p21 ^ 2
    - (5242880 : R) * a42 * q54 * p0 * hh ^ 2
    - (4718592 : R) * a42 * p21 * p0 * lam * hh ^ 2
    - (3145728 : R) * a42 * p21 * q31
    - (2359296 : R) * a42 * p1 ^ 2 * lam * hh
    + (15728640 : R) * a42 * p1 * p0 * hh ^ 2
    - (4194304 : R) * a42 * p1 * q42
    + (6291456 : R) * p32 ^ 2 * s2 * p1
    - (2359296 : R) * p32 ^ 2 * p0 * lam * hh
    + (6291456 : R) * p32 * s2 * p21 ^ 2
    - (6291456 : R) * p32 * b63 * p0 * hh
    - (5242880 : R) * p32 * q54 * p1
    - (4718592 : R) * p32 * p21 * p1 * lam
    + (15728640 : R) * p32 * p21 * p0 * hh
    + (7864320 : R) * p32 * p1 ^ 2
    - (8388608 : R) * s2 * p1 * p0 * hh ^ 2
    - (7340032 : R) * u2 * p21 * p0 * hh
    - (3670016 : R) * u2 * p1 ^ 2
    - (6291456 : R) * b63 * p21 * p1
    - (2621440 : R) * q54 * p21 ^ 2
    - (786432 : R) * p21 ^ 3 * lam
    + (7864320 : R) * p21 ^ 2 * p1
    + (2097152 : R) * p21 * q1 * hh
    + (4194304 : R) * p1 * q2
    + (1572864 : R) * p0 ^ 2 * lam * hh ^ 3
    + (6291456 : R) * p0 * q31 * hh

end BridgeMuJet610

/-! ## Jet factorizations of the cleared `μ` defect -/

section BridgeMuJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- On the globally merged jet the cleared `μ` defect factors exactly
as `h⁵⁹` times its factored order-`59` head plus `h` times the
tail. -/
theorem bridgeClearedMuDefect610_jet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedMuDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 59 *
        (bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 p2 q41 q3
            (Polynomial.C lambda) +
          h * bridgeMuJetTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1
            p0 q41 q3 q2 q1 (Polynomial.C lambda)) := by
  simp only [bridgeClearedMuDefect610, bridgeMuJetHead610,
    bridgeMuJetTail610]
  ring

set_option maxHeartbeats 400000000 in
/-- On the sibling-child deeper jet the cleared `μ` defect factors
exactly as `h⁶¹` times its order-`61` head plus `h` times the deep
tail. -/
theorem bridgeClearedMuDefect610_deepJet_factored
    (h w1 a42 p32 s2 u2 b63 q54 p21 p1 p0 q42 q31 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedMuDefect610 h (h ^ 5 * w1) (h ^ 4 * a42)
        (h ^ 2 * p32) (h * p21) p1 p0 (h ^ 8 * s2) (h ^ 6 * u2)
        (h ^ 5 * b63) (h ^ 4 * q54) (h ^ 2 * q42) (h * q31) q2 q1
        lambda =
      h ^ 61 *
        (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
            (Polynomial.C lambda) +
          h * bridgeMuDeepTail610 h w1 a42 p32 s2 u2 b63 q54 p21 p1
            p0 q42 q31 q2 q1 (Polynomial.C lambda)) := by
  simp only [bridgeClearedMuDefect610, bridgeMuDeepHead610,
    bridgeMuDeepTail610]
  ring

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

/-! ## Scalar consequences of the vanishing heads -/

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

/-! ## Finite local mu integral bridge packet -/

section NonzeroMuIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `μ` integral bridge: the `λ` bridge packet (the `ι`,
`κ` and `λ` packets reused opaquely) together with the weight-`65`
clearing of the degree-`2` first integral, its `h₀⁵⁹`-peeled factored
head, the chamber-free twenty-three-term reduction of the vanishing
head, the seven sibling-child descents with the `h₀⁶¹`-peeled deep
head and its honest split `p₃₂(a) = 0 ∨` first `λ`-loaded quotient
tie, and on the pinned complement child the honest split
`a₄₁(a) = 0` (collapsing that child) `∨` the first `q₃`-tie.  Every
child is preserved; none is closed. -/
theorem nonzeroFace610_linearRoot_muIntegralBridge
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
      (iotaK kappaMu lambdaNu muXi : k),
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
        bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C muXi * h0 ^ 65 ∧
        bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
              (q.coeff 3) (Polynomial.C lambda) +
            h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 6 ∧
        bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
          (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
          ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
          lambda = 0 ∧
        -(1120 : k) * (a41.eval a) ^ 6 * (w1.eval a)
        + (189 : k) * (a41.eval a) ^ 6 * lambda
        + (220 : k) * (a41.eval a) ^ 5 * (p32.eval a)
        + (588 : k) * (a41.eval a) ^ 5 * (u2.eval a)
        + (9200 : k) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * (w1.eval a)
        - (1260 : k) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * lambda
        - (600 : k) * (a41.eval a) ^ 4 * (q53.eval a)
        - (3360 : k) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (p32.eval a)
        - (3360 : k) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (u2.eval a)
        - (1920 : k) * (a41.eval a) ^ 3 * (q41.eval a) * (w1.eval a)
        + (576 : k) * (a41.eval a) ^ 3 * ((q.coeff 3).eval a)
        - (17280 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * (w1.eval a)
        + (2160 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * lambda
        + (2880 : k) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) * (q53.eval a)
        + (2304 : k) * (a41.eval a) ^ 2 * (p32.eval a) * (q41.eval a)
        + (4800 : k) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (p32.eval a)
        + (4032 : k) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (u2.eval a)
        + (4608 : k) * (a41.eval a) * ((p.coeff 2).eval a) * (q41.eval a) * (w1.eval a)
        - (2304 : k) * (a41.eval a) * ((p.coeff 2).eval a) * ((q.coeff 3).eval a)
        + (3840 : k) * ((p.coeff 2).eval a) ^ 3 * (w1.eval a)
        - (576 : k) * ((p.coeff 2).eval a) ^ 3 * lambda
        - (1920 : k) * ((p.coeff 2).eval a) ^ 2 * (q53.eval a)
        - (3072 : k) * ((p.coeff 2).eval a) * (p32.eval a) * (q41.eval a) = 0 ∧
        ((∃ a42 p21 s2 b63 q54 q42 q31 : k[X],
            (bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                  q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                  (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                  (Polynomial.C lambda) =
              Polynomial.C iotaK * h0 ^ 5) ∧
            a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
            s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
            q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
            (3 : k) * u2.eval a = (5 : k) * p32.eval a ∧
            p.coeff 4 = h0 ^ 4 * a42 ∧ p.coeff 2 = h0 * p21 ∧
            q.coeff 8 = h0 ^ 8 * s2 ∧ q.coeff 6 = h0 ^ 5 * b63 ∧
            q.coeff 5 = h0 ^ 4 * q54 ∧ q.coeff 4 = h0 ^ 2 * q42 ∧
            q.coeff 3 = h0 * q31 ∧
            (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
                  (Polynomial.C lambda) +
                h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
                  p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
                  (q.coeff 1) (Polynomial.C lambda) =
              Polynomial.C muXi * h0 ^ 4) ∧
            bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
              (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
              lambda = 0 ∧
            ((p32.eval a = 0 ∧ u2.eval a = 0) ∨
              (45 : k) * lambda * (p32.eval a) ^ 3 +
                  (144 : k) * b63.eval a * (p32.eval a) ^ 2 +
                  (240 : k) * p21.eval a * (p32.eval a) ^ 2 +
                  (288 : k) * p32.eval a * q42.eval a * w1.eval a -
                (400 : k) * (p32.eval a) ^ 3 * w1.eval a -
                  (144 : k) * p32.eval a * q31.eval a -
                  (384 : k) * p21.eval a * q42.eval a = 0)) ∨
          ((6 : k) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
            (6 : k) * b62.eval a - (5 : k) * (a41.eval a) ^ 2 = 0 ∧
            ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0) ∨
              (a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0 ∧ q41.eval a = 0) ∨
              ((324 : k) * q41.eval a = (35 : k) * (a41.eval a) ^ 3 ∧
                (15552 : k) * (q.coeff 3).eval a =
                  -(2943 : k) * lambda * (a41.eval a) ^ 3 +
                    (14040 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (1060 : k) * (a41.eval a) ^ 2 * p32.eval a -
                    (11340 : k) * (a41.eval a) ^ 2 * u2.eval a +
                    (14040 : k) * a41.eval a * q53.eval a)))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs, hUload,
    hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG, halt⟩ :=
    nonzeroFace610_linearRoot_lambdaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨muXi, hmupow⟩ :=
    nonzeroFace610_bridgeMuPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hmupowJet :
      bridgeClearedMuDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
          (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C muXi * h0 ^ 65 := by
    rw [← hw, ← ha4s, ← hp3', ← hs, ← hq7', ← hb6s, ← hq5', ← hq4']
    exact hmupow
  have hmupeel :
      bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
            (q.coeff 3) (Polynomial.C lambda) +
          h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
            (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
            (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
        Polynomial.C muXi * h0 ^ 6 := by
    have h59 : (h0 : k[X]) ^ 59 ≠ 0 := pow_ne_zero 59 hh0
    apply mul_left_cancel₀ h59
    rw [← bridgeClearedMuDefect610_jet_factored h0 w1 a41 p32 s1 u2
      b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
      (q.coeff 2) (q.coeff 1) lambda]
    rw [hmupowJet]
    ring
  have hmuheadeval :
      bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
        (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
        ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
        lambda = 0 := by
    have hev := congrArg (Polynomial.eval a) hmupeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeMuJetHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hUz : (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a +
      (30 : k) * (p.coeff 2).eval a = 0 := by
    linear_combination hUload +
      ((9 : k) * lambda - (20 : k) * w1.eval a) * hp31z
  have hmuR22 :=
    bridgeMu_chamberFreeReduction610 (w1.eval a) (a41.eval a)
      (p32.eval a) (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
      ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a) lambda
      hmuheadeval hMs hUz
  have h3ne : (3 : k) ≠ 0 := by norm_num
  refine ⟨w1, a41, s1, u1, p31, b62, q52, p32, u2, q53, q41, iotaK,
    kappaMu, lambdaNu, muXi, hw, ha4s, hp3, hs, hu, hb6s, hq5, hMs,
    hUload, hrow, hroweval, hipow, hipeel, hiheadeval, hkpow, hkpeel,
    hkheadeval, hlpow, hlpeel, hlheadeval, hp31z, hu1z, hq52z, hq4z,
    hp3', hq7', hq5', hq4', hldeepPeel, hldeepHeadEval, hG,
    hmupow, hmupeel, hmuheadeval, hmuR22, ?_⟩
  rcases halt with ⟨hileft, ha41z, hp2z, hs1z, hb62z, hq41z, hq53z,
      hq3z, hu2tie⟩ | ⟨hp2pin, hb62pin, hcd⟩
  · obtain ⟨a42, ha42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 a41 a hh0degree
        hroot ha41z
    obtain ⟨p21, hp21⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 2) a
        hh0degree hroot hp2z
    obtain ⟨s2, hs2⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s1 a hh0degree
        hroot hs1z
    obtain ⟨b63, hb63⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 b62 a hh0degree
        hroot hb62z
    obtain ⟨q42, hq42⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q41 a hh0degree
        hroot hq41z
    obtain ⟨q54, hq54⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 q53 a hh0degree
        hroot hq53z
    obtain ⟨q31, hq31⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 3) a
        hh0degree hroot hq3z
    have hp4deep : p.coeff 4 = h0 ^ 4 * a42 := by
      rw [ha4s, ha42]
      ring
    have hq8deep : q.coeff 8 = h0 ^ 8 * s2 := by
      rw [hs, hs2]
      ring
    have hq6deep : q.coeff 6 = h0 ^ 5 * b63 := by
      rw [hb6s, hb63]
      ring
    have hq5deep2 : q.coeff 5 = h0 ^ 4 * q54 := by
      rw [hq5', hq54]
      ring
    have hq4deep2 : q.coeff 4 = h0 ^ 2 * q42 := by
      rw [hq4', hq42]
      ring
    have hmupowDeep :
        bridgeClearedMuDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 4 * a42)
            (h0 ^ 2 * p32) (h0 * p21) (p.coeff 1) (p.coeff 0)
            (h0 ^ 8 * s2) (h0 ^ 6 * u2) (h0 ^ 5 * b63) (h0 ^ 4 * q54)
            (h0 ^ 2 * q42) (h0 * q31) (q.coeff 2) (q.coeff 1)
            lambda =
          Polynomial.C muXi * h0 ^ 65 := by
      rw [← hw, ← hp4deep, ← hp3', ← hp21, ← hq8deep, ← hq7',
        ← hq6deep, ← hq5deep2, ← hq4deep2, ← hq31]
      exact hmupow
    have hmuDeepPeel :
        bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
              (Polynomial.C lambda) +
            h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
              p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
              (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 4 := by
      have h61 : (h0 : k[X]) ^ 61 ≠ 0 := pow_ne_zero 61 hh0
      apply mul_left_cancel₀ h61
      rw [← bridgeClearedMuDefect610_deepJet_factored h0 w1 a42 p32
        s2 u2 b63 q54 p21 (p.coeff 1) (p.coeff 0) q42 q31
        (q.coeff 2) (q.coeff 1) lambda]
      rw [hmupowDeep]
      ring
    have hmuDeepHeadEval :
        bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
          (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
          lambda = 0 := by
      have hev := congrArg (Polynomial.eval a) hmuDeepPeel
      have h4z : (0 : k) ^ 4 = 0 := by norm_num
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, hroot,
        bridgeMuDeepHead610_eval, h4z, mul_zero, zero_mul,
        add_zero] at hev
      exact hev
    have hsplit :=
      bridgeMu_siblingDeepSplit610 (w1.eval a) (p32.eval a)
        (u2.eval a) (b63.eval a) (p21.eval a) (q42.eval a)
        (q31.eval a) lambda hmuDeepHeadEval hu2tie
    exact Or.inl ⟨a42, p21, s2, b63, q54, q42, q31, hileft, ha41z,
      hp2z, hs1z, hb62z, hq41z, hq53z, hq3z, hu2tie, hp4deep, hp21,
      hq8deep, hq6deep, hq5deep2, hq4deep2, hq31, hmuDeepPeel,
      hmuDeepHeadEval, hsplit⟩
  · rcases hcd with ⟨ha41z, hp2z, hb62z⟩ | hq41pin
    · exact Or.inr ⟨hp2pin, hb62pin, Or.inl ⟨ha41z, hp2z, hb62z⟩⟩
    · rcases bridgeMu_complementSplit610 (w1.eval a) (a41.eval a)
          (p32.eval a) (u2.eval a) (q53.eval a) (q41.eval a)
          ((q.coeff 3).eval a) ((p.coeff 2).eval a) lambda hmuR22
          hp2pin hq41pin with ha41z | htie
      · have hp2z : (p.coeff 2).eval a = 0 := by
          linear_combination (1 / 6 : k) * hp2pin +
            ((1 / 6 : k) * a41.eval a) * ha41z
        have hb62z : b62.eval a = 0 := by
          linear_combination (1 / 6 : k) * hb62pin +
            ((5 / 6 : k) * a41.eval a) * ha41z
        have hq41z : q41.eval a = 0 := by
          linear_combination (1 / 324 : k) * hq41pin +
            ((35 / 324 : k) * (a41.eval a) ^ 2) * ha41z
        exact Or.inr ⟨hp2pin, hb62pin,
          Or.inr (Or.inl ⟨ha41z, hp2z, hb62z, hq41z⟩)⟩
      · exact Or.inr ⟨hp2pin, hb62pin, Or.inr (Or.inr ⟨hq41pin, htie⟩)⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing `μ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the `λ` bridge packet with the weight-`65`
clearing of the degree-`2` first integral, its `h₀⁵⁹`-peeled head and
chamber-free twenty-three-term root reduction, the seven
sibling-child descents with the `h₀⁶¹`-peeled deep head and its
honest split, and the pinned complement child refined by the honest
split `a₄₁(a) = 0 ∨` first `q₃`-tie.  The ground constants `iotaK`,
`kappaMu`, `lambdaNu` and `muXi` are preserved, not cleared, and no
surviving child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_muIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu lambdaNu muXi : K)
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
        bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C muXi * h0 ^ 65 ∧
        bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
              (q.coeff 3) (Polynomial.C lambda) +
            h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 6 ∧
        bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
          (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
          ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
          lambda = 0 ∧
        -(1120 : K) * (a41.eval a) ^ 6 * (w1.eval a)
        + (189 : K) * (a41.eval a) ^ 6 * lambda
        + (220 : K) * (a41.eval a) ^ 5 * (p32.eval a)
        + (588 : K) * (a41.eval a) ^ 5 * (u2.eval a)
        + (9200 : K) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * (w1.eval a)
        - (1260 : K) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * lambda
        - (600 : K) * (a41.eval a) ^ 4 * (q53.eval a)
        - (3360 : K) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (p32.eval a)
        - (3360 : K) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (u2.eval a)
        - (1920 : K) * (a41.eval a) ^ 3 * (q41.eval a) * (w1.eval a)
        + (576 : K) * (a41.eval a) ^ 3 * ((q.coeff 3).eval a)
        - (17280 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * (w1.eval a)
        + (2160 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * lambda
        + (2880 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) * (q53.eval a)
        + (2304 : K) * (a41.eval a) ^ 2 * (p32.eval a) * (q41.eval a)
        + (4800 : K) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (p32.eval a)
        + (4032 : K) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (u2.eval a)
        + (4608 : K) * (a41.eval a) * ((p.coeff 2).eval a) * (q41.eval a) * (w1.eval a)
        - (2304 : K) * (a41.eval a) * ((p.coeff 2).eval a) * ((q.coeff 3).eval a)
        + (3840 : K) * ((p.coeff 2).eval a) ^ 3 * (w1.eval a)
        - (576 : K) * ((p.coeff 2).eval a) ^ 3 * lambda
        - (1920 : K) * ((p.coeff 2).eval a) ^ 2 * (q53.eval a)
        - (3072 : K) * ((p.coeff 2).eval a) * (p32.eval a) * (q41.eval a) = 0 ∧
        ((∃ a42 p21 s2 b63 q54 q42 q31 : K[X],
            (bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                  q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                  (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                  (Polynomial.C lambda) =
              Polynomial.C iotaK * h0 ^ 5) ∧
            a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
            s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
            q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
            (3 : K) * u2.eval a = (5 : K) * p32.eval a ∧
            p.coeff 4 = h0 ^ 4 * a42 ∧ p.coeff 2 = h0 * p21 ∧
            q.coeff 8 = h0 ^ 8 * s2 ∧ q.coeff 6 = h0 ^ 5 * b63 ∧
            q.coeff 5 = h0 ^ 4 * q54 ∧ q.coeff 4 = h0 ^ 2 * q42 ∧
            q.coeff 3 = h0 * q31 ∧
            (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
                  (Polynomial.C lambda) +
                h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
                  p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
                  (q.coeff 1) (Polynomial.C lambda) =
              Polynomial.C muXi * h0 ^ 4) ∧
            bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
              (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
              lambda = 0 ∧
            ((p32.eval a = 0 ∧ u2.eval a = 0) ∨
              (45 : K) * lambda * (p32.eval a) ^ 3 +
                  (144 : K) * b63.eval a * (p32.eval a) ^ 2 +
                  (240 : K) * p21.eval a * (p32.eval a) ^ 2 +
                  (288 : K) * p32.eval a * q42.eval a * w1.eval a -
                (400 : K) * (p32.eval a) ^ 3 * w1.eval a -
                  (144 : K) * p32.eval a * q31.eval a -
                  (384 : K) * p21.eval a * q42.eval a = 0)) ∨
          ((6 : K) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
            (6 : K) * b62.eval a - (5 : K) * (a41.eval a) ^ 2 = 0 ∧
            ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0) ∨
              (a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0 ∧ q41.eval a = 0) ∨
              ((324 : K) * q41.eval a = (35 : K) * (a41.eval a) ^ 3 ∧
                (15552 : K) * (q.coeff 3).eval a =
                  -(2943 : K) * lambda * (a41.eval a) ^ 3 +
                    (14040 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (1060 : K) * (a41.eval a) ^ 2 * p32.eval a -
                    (11340 : K) * (a41.eval a) ^ 2 * u2.eval a +
                    (14040 : K) * a41.eval a * q53.eval a)))) ∧
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
    q41', iotaK, kappaMu, lambdaNu, muXi, hwN, ha4sN, hp3N, hsN, huN,
    hb6sN, hq5N, hMs', hUload', hrow, hroweval, hipow, hipeel,
    hiheadeval, hkpow, hkpeel, hkheadeval, hlpow, hlpeel, hlheadeval,
    hp31z, hu1z, hq52z, hq4z, hp3deep, hq7deep, hq5deep, hq4deep,
    hldeepPeel, hldeepHeadEval, hG, hmupow, hmupeel, hmuheadeval,
    hmuR22, halt⟩ :=
    nonzeroFace610_linearRoot_muIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, lambdaNu, muXi, w1', a41',
    s1', u1', p31', b62', q52', p32', u2', q53', q41', hh0, hlambda,
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
    hlpeel, hlheadeval, hldeepPeel, hldeepHeadEval, hG, hmupow,
    hmupeel, hmuheadeval, hmuR22, halt, hN'⟩

end NonzeroMuIntegralBridge610

#print axioms nonzeroFace610_linearRoot_muIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_muIntegralBridge

#print axioms nonzeroFace610_bridgeMuPowerRelation

end Max11DegreeRoutes
