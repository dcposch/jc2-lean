import Fable610ScaleTwoTerminalIntegralClosureScratch

/-! # Compatible kappa integral bridge for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h₀²` and `N = 5 p₅ H² - 3 q₉ = λ h₀⁹`
with `h₀.natDegree = 1`, the terminal integral closure spent the
degree-`5` first integral `ι`; the next genuinely unused integral row
is the degree-`4` first integral `κ`, whose construction needs the
degree-`6` `θ` tower.  The scale-zero eighth/ninth/tenth defect
scratches state that tower and the `κ` clearing, but they collide with
canonical scale-two declarations, so nothing is imported from them:
this file restates on the compatible scale-two chain, with
`terminal`/`_bridge` names, exactly the missing pieces — the depressed
decic `z¹` coordinate and its ninth-power clearing, the degree-`6` and
degree-`4` depressed differential rows, the degree-`6` integral `θ`
with `d θ = 0`, and the degree-`4` integral `κ` with `d κ = 0` — and
rederives the weight-`55` power relation
`bridgeClearedKappaDefect610 = C kappaMu · h₀⁵⁵` directly from the
source differential rows already in the canonical ancestry (rows `13`
through `7`, the bridge row `5`, and the two rows restated here).  The
spent `ι` packet is reused opaquely; its weight-`50` numerator is never
re-expanded.

On the fifteenth-face jet `p₅ = h₀⁵ w₁`, `p₄ = h₀³ a₄₁`,
`p₃ = h₀ p₃₁`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁵ u₁`, `q₆ = h₀⁴ b₆₂`,
`q₅ = h₀² q₅₂` the numerator factors exactly through `h₀⁴⁸`, seven
orders below the defect weight, with fully factored first head
`4837294080 p₃₁ (264 p₃₁² s₁ + 693 a₄₁ p₃₁ u₁ - 935 a₄₁ p₃₁²
- 432 a₄₁ q₄ - 270 p₃₁ q₅₂)`; the peel is
`head + h₀ · tail = C kappaMu · h₀⁷`, so the head vanishes at the
root, and modulo the tenth-face root laws alone it reduces,
chamber-free, to `a₄₁(a) p₃₁(a)³ = 0` — the honest split
`a₄₁(a) = 0 ∨ p₃₁(a) = 0`, a relation the `ι` heads never reached.

Combined with the four exact terminal-closure children: the two
`p₃₁(a) = 0` sibling children and the pinned `p₃₁(a) = 0` complement
child absorb the head through its overall `p₃₁` factor and are
retained unchanged.  On the `p₃₁(a) ≠ 0` child the split forces
`a₄₁(a) = 0`, the retained core `5 a₄₁² + 2 p₃₁ w₁ = 0` forces
`w₁(a) = 0`, and the remaining ground relations collapse to the pins
`80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)`, which subsume all
three original relations; the retained `ψ₂` value collapses to
`ψ₂(a) = -209952 λ p₁(a)`, under which the retained boundary
elimination reproduces exactly the inhomogeneous degree-`0` Keller row
`p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`, the sole inhomogeneous constraint
left on that child.

No child is closed, because none is contradicted — the Keller boundary
relation lives on the fresh coordinates `p₀, p₁, q₀, q₁`.  The honest
residual is that single boundary relation with the preserved ground
constants `ζ, η, iotaK, kappaMu` and the open aligned face `N = 0`.
The next unused integral row is the degree-`3` first integral; the
next unused aligned row on `N = 0` is the degree-`10` row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Depressed decic `z¹` coordinate and the `θ`/`κ` residuals -/

section BridgeKappaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z¹` coefficient. -/
def terminalDepressedW610 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  -10 * r ^ 9 + 9 * (b9 / h ^ 9) * r ^ 8 -
    8 * (b8 / h ^ 8) * r ^ 7 + 7 * (b7 / h ^ 7) * r ^ 6 -
    6 * (b6 / h ^ 6) * r ^ 5 + 5 * (b5 / h ^ 5) * r ^ 4 -
    4 * (b4 / h ^ 4) * r ^ 3 + 3 * (b3 / h ^ 3) * r ^ 2 -
    2 * (b2 / h ^ 2) * r + b1 / h

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

/-- Exact denominator clearing for the decic `z¹` coordinate on the
ninth-power face. -/
theorem terminalDepressedW610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    terminalDepressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 b1 =
      (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
          144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
          3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
          93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
          1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
        (5038848 * h ^ 45) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [terminalDepressedW610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      -10 * (a5 / (6 * h ^ 5)) ^ 9 +
          9 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 8 -
        8 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 7 +
          7 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 6 -
        6 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 5 +
          5 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 4 -
        4 * (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 3 +
          3 * (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) ^ 2 -
        2 * (b2 / h ^ 2) * (a5 / (6 * h ^ 5)) + b1 / h =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh45, h5038848]
    ring
  exact hrewrite


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

set_option maxHeartbeats 8000000 in
/-- Polynomial numerator of `3761479876608 h⁵⁵ κ` on the ninth-power face. -/
def bridgeClearedKappaDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    - (231612681800 : F[X]) * a5 ^ 11
    + (114648277491 : F[X]) * a5 ^ 10 * h ^ 5 * Polynomial.C lambda
    + (2018963377200 : F[X]) * a4 * a5 ^ 9 * h ^ 6
    + (346108007520 : F[X]) * a5 ^ 9 * b8 * h ^ 2
    - (1168114525380 : F[X]) * a4 * a5 ^ 8 * h ^ 11 * Polynomial.C lambda
    - (2071125045000 : F[X]) * a3 * a5 ^ 8 * h ^ 12
    - (347949007560 : F[X]) * a5 ^ 8 * b7 * h ^ 8
    - (5302080115200 : F[X]) * a4 ^ 2 * a5 ^ 7 * h ^ 12
    - (3181248069120 : F[X]) * a4 * a5 ^ 7 * b8 * h ^ 8
    + (1192968025920 : F[X]) * a3 * a5 ^ 7 * h ^ 17 * Polynomial.C lambda
    + (2133763948800 : F[X]) * a2 * a5 ^ 7 * h ^ 18
    + (349161373440 : F[X]) * a5 ^ 7 * b6 * h ^ 14
    + (4175388090720 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 17 * Polynomial.C lambda
    + (8826023606400 : F[X]) * a3 * a4 * a5 ^ 6 * h ^ 18
    + (2851484549760 : F[X]) * a4 * a5 ^ 6 * b7 * h ^ 14
    + (3258839485440 : F[X]) * a3 * a5 ^ 6 * b8 * h ^ 14
    - (1222064807040 : F[X]) * a2 * a5 ^ 6 * h ^ 23 * Polynomial.C lambda
    - (2211355365120 : F[X]) * a1 * a5 ^ 6 * h ^ 24
    - (349161373440 : F[X]) * a5 ^ 6 * b5 * h ^ 20
    + (2715699571200 : F[X]) * a4 ^ 3 * a5 ^ 5 * h ^ 18
    + (9776518456320 : F[X]) * a4 ^ 2 * a5 ^ 5 * b8 * h ^ 14
    - (7332388842240 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    - (6983227468800 : F[X]) * a2 * a4 * a5 ^ 5 * h ^ 24
    - (2513961888768 : F[X]) * a4 * a5 ^ 5 * b6 * h ^ 20
    - (3491613734400 : F[X]) * a3 ^ 2 * a5 ^ 5 * h ^ 24
    - (2932955536896 : F[X]) * a3 * a5 ^ 5 * b7 * h ^ 20
    - (3351949185024 : F[X]) * a2 * a5 ^ 5 * b8 * h ^ 20
    + (1256980944384 : F[X]) * a1 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    + (2311689093120 : F[X]) * a0 * a5 ^ 5 * h ^ 30
    + (346753363968 : F[X]) * a5 ^ 5 * b4 * h ^ 26
    - (6110324035200 : F[X]) * a4 ^ 3 * a5 ^ 4 * h ^ 23 * Polynomial.C lambda
    - (1745806867200 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 24
    - (7332388842240 : F[X]) * a4 ^ 2 * a5 ^ 4 * b7 * h ^ 20
    - (16759745925120 : F[X]) * a3 * a4 * a5 ^ 4 * b8 * h ^ 20
    + (6284904721920 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (5056819891200 : F[X]) * a1 * a4 * a5 ^ 4 * h ^ 30
    + (2167208524800 : F[X]) * a4 * a5 ^ 4 * b5 * h ^ 26
    + (3142452360960 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (5056819891200 : F[X]) * a2 * a3 * a5 ^ 4 * h ^ 30
    + (2600650229760 : F[X]) * a3 * a5 ^ 4 * b6 * h ^ 26
    + (3034091934720 : F[X]) * a2 * a5 ^ 4 * b7 * h ^ 26
    + (3467533639680 : F[X]) * a1 * a5 ^ 4 * b8 * h ^ 26
    - (1300325114880 : F[X]) * a0 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (339215247360 : F[X]) * a5 ^ 4 * b3 * h ^ 32
    + (4655484979200 : F[X]) * a4 ^ 4 * a5 ^ 3 * h ^ 24
    - (11173163950080 : F[X]) * a4 ^ 3 * a5 ^ 3 * b8 * h ^ 20
    + (12569809443840 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    - (2889611366400 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 30
    + (5201300459520 : F[X]) * a4 ^ 2 * a5 ^ 3 * b6 * h ^ 26
    - (2889611366400 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 30
    + (12136367738880 : F[X]) * a3 * a4 * a5 ^ 3 * b7 * h ^ 26
    + (13870134558720 : F[X]) * a2 * a4 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (3015246643200 : F[X]) * a0 * a4 * a5 ^ 3 * h ^ 36
    - (1809147985920 : F[X]) * a4 * a5 ^ 3 * b4 * h ^ 32
    + (6935067279360 : F[X]) * a3 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (3015246643200 : F[X]) * a1 * a3 * a5 ^ 3 * h ^ 36
    - (2261434982400 : F[X]) * a3 * a5 ^ 3 * b5 * h ^ 32
    - (1507623321600 : F[X]) * a2 ^ 2 * a5 ^ 3 * h ^ 36
    - (2713721978880 : F[X]) * a2 * a5 ^ 3 * b6 * h ^ 32
    - (3166008975360 : F[X]) * a1 * a5 ^ 3 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a0 * a5 ^ 3 * b8 * h ^ 32
    + (319261409280 : F[X]) * a5 ^ 3 * b2 * h ^ 38
    + (3142452360960 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 29 * Polynomial.C lambda
    - (15892862515200 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 30
    + (6068183869440 : F[X]) * a4 ^ 3 * a5 ^ 2 * b7 * h ^ 26
    + (20805201838080 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (7801950689280 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (5653587456000 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    - (3392152473600 : F[X]) * a4 ^ 2 * a5 ^ 2 * b5 * h ^ 32
    - (7801950689280 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (11307174912000 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * h ^ 36
    - (8141165936640 : F[X]) * a3 * a4 * a5 ^ 2 * b6 * h ^ 32
    - (9498026926080 : F[X]) * a2 * a4 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a1 * a4 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a0 * a4 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (1436676341760 : F[X]) * a4 * a5 ^ 2 * b3 * h ^ 38
    + (1884529152000 : F[X]) * a3 ^ 3 * a5 ^ 2 * h ^ 36
    - (4749013463040 : F[X]) * a3 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a3 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a1 * a3 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (798153523200 : F[X]) * a0 * a3 * a5 ^ 2 * h ^ 42
    + (1915568455680 : F[X]) * a3 * a5 ^ 2 * b4 * h ^ 38
    + (2035291484160 : F[X]) * a2 ^ 2 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (798153523200 : F[X]) * a1 * a2 * a5 ^ 2 * h ^ 42
    + (2394460569600 : F[X]) * a2 * a5 ^ 2 * b5 * h ^ 38
    + (2873352683520 : F[X]) * a1 * a5 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a0 * a5 ^ 2 * b7 * h ^ 38
    - (261213880320 : F[X]) * a5 ^ 2 * b1 * h ^ 44
    - (2889611366400 : F[X]) * a4 ^ 5 * a5 * h ^ 30
    + (3467533639680 : F[X]) * a4 ^ 4 * a5 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 35 * Polynomial.C lambda
    + (10553363251200 : F[X]) * a2 * a4 ^ 3 * a5 * h ^ 36
    - (2713721978880 : F[X]) * a4 ^ 3 * a5 * b6 * h ^ 32
    + (15830044876800 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 36
    - (9498026926080 : F[X]) * a3 * a4 ^ 2 * a5 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a4 ^ 2 * a5 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    - (6385228185600 : F[X]) * a0 * a4 ^ 2 * a5 * h ^ 42
    + (1915568455680 : F[X]) * a4 ^ 2 * a5 * b4 * h ^ 38
    - (10854887915520 : F[X]) * a3 ^ 2 * a4 * a5 * b8 * h ^ 32
    + (8141165936640 : F[X]) * a2 * a3 * a4 * a5 * h ^ 41 * Polynomial.C lambda
    - (12770456371200 : F[X]) * a1 * a3 * a4 * a5 * h ^ 42
    + (4788921139200 : F[X]) * a3 * a4 * a5 * b5 * h ^ 38
    - (6385228185600 : F[X]) * a2 ^ 2 * a4 * a5 * h ^ 42
    + (5746705367040 : F[X]) * a2 * a4 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a1 * a4 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a0 * a4 * a5 * b8 * h ^ 38
    - (1044855521280 : F[X]) * a4 * a5 * b2 * h ^ 44
    + (1356860989440 : F[X]) * a3 ^ 3 * a5 * h ^ 41 * Polynomial.C lambda
    - (6385228185600 : F[X]) * a2 * a3 ^ 2 * a5 * h ^ 42
    + (2873352683520 : F[X]) * a3 ^ 2 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a2 * a3 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a1 * a3 * a5 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a0 * a3 * a5 * h ^ 47 * Polynomial.C lambda
    - (1567283281920 : F[X]) * a3 * a5 * b3 * h ^ 44
    + (3831136911360 : F[X]) * a2 ^ 2 * a5 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a1 * a2 * a5 * h ^ 47 * Polynomial.C lambda
    + (1741425868800 : F[X]) * a0 * a2 * a5 * h ^ 48
    - (2089711042560 : F[X]) * a2 * a5 * b4 * h ^ 44
    + (870712934400 : F[X]) * a1 ^ 2 * a5 * h ^ 48
    - (2612138803200 : F[X]) * a1 * a5 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a0 * a5 * b6 * h ^ 44
    - (260065022976 : F[X]) * a4 ^ 5 * h ^ 35 * Polynomial.C lambda
    + (4334417049600 : F[X]) * a3 * a4 ^ 4 * h ^ 36
    - (791502243840 : F[X]) * a4 ^ 4 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a3 * a4 ^ 3 * b8 * h ^ 32
    + (1356860989440 : F[X]) * a2 * a4 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (4522869964800 : F[X]) * a1 * a4 ^ 3 * h ^ 42
    + (798153523200 : F[X]) * a4 ^ 3 * b5 * h ^ 38
    + (2035291484160 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (13568609894400 : F[X]) * a2 * a3 * a4 ^ 2 * h ^ 42
    + (2873352683520 : F[X]) * a3 * a4 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a2 * a4 ^ 2 * b7 * h ^ 38
    + (3831136911360 : F[X]) * a1 * a4 ^ 2 * b8 * h ^ 38
    - (1436676341760 : F[X]) * a0 * a4 ^ 2 * h ^ 47 * Polynomial.C lambda
    - (783641640960 : F[X]) * a4 ^ 2 * b3 * h ^ 44
    - (4522869964800 : F[X]) * a3 ^ 3 * a4 * h ^ 42
    + (3352244797440 : F[X]) * a3 ^ 2 * a4 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a2 * a3 * a4 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a1 * a3 * a4 * h ^ 47 * Polynomial.C lambda
    + (9577842278400 : F[X]) * a0 * a3 * a4 * h ^ 48
    - (2089711042560 : F[X]) * a3 * a4 * b4 * h ^ 44
    - (1436676341760 : F[X]) * a2 ^ 2 * a4 * h ^ 47 * Polynomial.C lambda
    + (9577842278400 : F[X]) * a1 * a2 * a4 * h ^ 48
    - (2612138803200 : F[X]) * a2 * a4 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a1 * a4 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a0 * a4 * b7 * h ^ 44
    + (626913312768 : F[X]) * a4 * b1 * h ^ 50
    + (1277045637120 : F[X]) * a3 ^ 3 * b8 * h ^ 38
    - (1436676341760 : F[X]) * a2 * a3 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (4788921139200 : F[X]) * a1 * a3 ^ 2 * h ^ 48
    - (1306069401600 : F[X]) * a3 ^ 2 * b5 * h ^ 44
    + (4788921139200 : F[X]) * a2 ^ 2 * a3 * h ^ 48
    - (3134566563840 : F[X]) * a2 * a3 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a1 * a3 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a0 * a3 * b8 * h ^ 44
    + (1253826625536 : F[X]) * a3 * b2 * h ^ 50
    - (1828497162240 : F[X]) * a2 ^ 2 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a1 * a2 * b8 * h ^ 44
    + (1567283281920 : F[X]) * a0 * a2 * h ^ 53 * Polynomial.C lambda
    + (1880739938304 : F[X]) * a2 * b3 * h ^ 50
    + (783641640960 : F[X]) * a1 ^ 2 * h ^ 53 * Polynomial.C lambda
    - (5224277606400 : F[X]) * a0 * a1 * h ^ 54
    + (2507653251072 : F[X]) * a1 * b4 * h ^ 50
    + (3134566563840 : F[X]) * a0 * b5 * h ^ 50

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral `κ` of the degree-`4` row against `h⁵⁵`
on the ninth-power face. -/
theorem bridgeKappaDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (3761479876608 : F) * h ^ 55 *
        bridgeKappaResidual610
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
    - (231612681800 : F) * a5 ^ 11
    + (114648277491 : F) * a5 ^ 10 * h ^ 5 * lambda
    + (2018963377200 : F) * a4 * a5 ^ 9 * h ^ 6
    + (346108007520 : F) * a5 ^ 9 * b8 * h ^ 2
    - (1168114525380 : F) * a4 * a5 ^ 8 * h ^ 11 * lambda
    - (2071125045000 : F) * a3 * a5 ^ 8 * h ^ 12
    - (347949007560 : F) * a5 ^ 8 * b7 * h ^ 8
    - (5302080115200 : F) * a4 ^ 2 * a5 ^ 7 * h ^ 12
    - (3181248069120 : F) * a4 * a5 ^ 7 * b8 * h ^ 8
    + (1192968025920 : F) * a3 * a5 ^ 7 * h ^ 17 * lambda
    + (2133763948800 : F) * a2 * a5 ^ 7 * h ^ 18
    + (349161373440 : F) * a5 ^ 7 * b6 * h ^ 14
    + (4175388090720 : F) * a4 ^ 2 * a5 ^ 6 * h ^ 17 * lambda
    + (8826023606400 : F) * a3 * a4 * a5 ^ 6 * h ^ 18
    + (2851484549760 : F) * a4 * a5 ^ 6 * b7 * h ^ 14
    + (3258839485440 : F) * a3 * a5 ^ 6 * b8 * h ^ 14
    - (1222064807040 : F) * a2 * a5 ^ 6 * h ^ 23 * lambda
    - (2211355365120 : F) * a1 * a5 ^ 6 * h ^ 24
    - (349161373440 : F) * a5 ^ 6 * b5 * h ^ 20
    + (2715699571200 : F) * a4 ^ 3 * a5 ^ 5 * h ^ 18
    + (9776518456320 : F) * a4 ^ 2 * a5 ^ 5 * b8 * h ^ 14
    - (7332388842240 : F) * a3 * a4 * a5 ^ 5 * h ^ 23 * lambda
    - (6983227468800 : F) * a2 * a4 * a5 ^ 5 * h ^ 24
    - (2513961888768 : F) * a4 * a5 ^ 5 * b6 * h ^ 20
    - (3491613734400 : F) * a3 ^ 2 * a5 ^ 5 * h ^ 24
    - (2932955536896 : F) * a3 * a5 ^ 5 * b7 * h ^ 20
    - (3351949185024 : F) * a2 * a5 ^ 5 * b8 * h ^ 20
    + (1256980944384 : F) * a1 * a5 ^ 5 * h ^ 29 * lambda
    + (2311689093120 : F) * a0 * a5 ^ 5 * h ^ 30
    + (346753363968 : F) * a5 ^ 5 * b4 * h ^ 26
    - (6110324035200 : F) * a4 ^ 3 * a5 ^ 4 * h ^ 23 * lambda
    - (1745806867200 : F) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 24
    - (7332388842240 : F) * a4 ^ 2 * a5 ^ 4 * b7 * h ^ 20
    - (16759745925120 : F) * a3 * a4 * a5 ^ 4 * b8 * h ^ 20
    + (6284904721920 : F) * a2 * a4 * a5 ^ 4 * h ^ 29 * lambda
    + (5056819891200 : F) * a1 * a4 * a5 ^ 4 * h ^ 30
    + (2167208524800 : F) * a4 * a5 ^ 4 * b5 * h ^ 26
    + (3142452360960 : F) * a3 ^ 2 * a5 ^ 4 * h ^ 29 * lambda
    + (5056819891200 : F) * a2 * a3 * a5 ^ 4 * h ^ 30
    + (2600650229760 : F) * a3 * a5 ^ 4 * b6 * h ^ 26
    + (3034091934720 : F) * a2 * a5 ^ 4 * b7 * h ^ 26
    + (3467533639680 : F) * a1 * a5 ^ 4 * b8 * h ^ 26
    - (1300325114880 : F) * a0 * a5 ^ 4 * h ^ 35 * lambda
    - (339215247360 : F) * a5 ^ 4 * b3 * h ^ 32
    + (4655484979200 : F) * a4 ^ 4 * a5 ^ 3 * h ^ 24
    - (11173163950080 : F) * a4 ^ 3 * a5 ^ 3 * b8 * h ^ 20
    + (12569809443840 : F) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 29 * lambda
    - (2889611366400 : F) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 30
    + (5201300459520 : F) * a4 ^ 2 * a5 ^ 3 * b6 * h ^ 26
    - (2889611366400 : F) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 30
    + (12136367738880 : F) * a3 * a4 * a5 ^ 3 * b7 * h ^ 26
    + (13870134558720 : F) * a2 * a4 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F) * a1 * a4 * a5 ^ 3 * h ^ 35 * lambda
    - (3015246643200 : F) * a0 * a4 * a5 ^ 3 * h ^ 36
    - (1809147985920 : F) * a4 * a5 ^ 3 * b4 * h ^ 32
    + (6935067279360 : F) * a3 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F) * a2 * a3 * a5 ^ 3 * h ^ 35 * lambda
    - (3015246643200 : F) * a1 * a3 * a5 ^ 3 * h ^ 36
    - (2261434982400 : F) * a3 * a5 ^ 3 * b5 * h ^ 32
    - (1507623321600 : F) * a2 ^ 2 * a5 ^ 3 * h ^ 36
    - (2713721978880 : F) * a2 * a5 ^ 3 * b6 * h ^ 32
    - (3166008975360 : F) * a1 * a5 ^ 3 * b7 * h ^ 32
    - (3618295971840 : F) * a0 * a5 ^ 3 * b8 * h ^ 32
    + (319261409280 : F) * a5 ^ 3 * b2 * h ^ 38
    + (3142452360960 : F) * a4 ^ 4 * a5 ^ 2 * h ^ 29 * lambda
    - (15892862515200 : F) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 30
    + (6068183869440 : F) * a4 ^ 3 * a5 ^ 2 * b7 * h ^ 26
    + (20805201838080 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (7801950689280 : F) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 35 * lambda
    + (5653587456000 : F) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    - (3392152473600 : F) * a4 ^ 2 * a5 ^ 2 * b5 * h ^ 32
    - (7801950689280 : F) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 35 * lambda
    + (11307174912000 : F) * a2 * a3 * a4 * a5 ^ 2 * h ^ 36
    - (8141165936640 : F) * a3 * a4 * a5 ^ 2 * b6 * h ^ 32
    - (9498026926080 : F) * a2 * a4 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F) * a1 * a4 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F) * a0 * a4 * a5 ^ 2 * h ^ 41 * lambda
    + (1436676341760 : F) * a4 * a5 ^ 2 * b3 * h ^ 38
    + (1884529152000 : F) * a3 ^ 3 * a5 ^ 2 * h ^ 36
    - (4749013463040 : F) * a3 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F) * a2 * a3 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F) * a1 * a3 * a5 ^ 2 * h ^ 41 * lambda
    + (798153523200 : F) * a0 * a3 * a5 ^ 2 * h ^ 42
    + (1915568455680 : F) * a3 * a5 ^ 2 * b4 * h ^ 38
    + (2035291484160 : F) * a2 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    + (798153523200 : F) * a1 * a2 * a5 ^ 2 * h ^ 42
    + (2394460569600 : F) * a2 * a5 ^ 2 * b5 * h ^ 38
    + (2873352683520 : F) * a1 * a5 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F) * a0 * a5 ^ 2 * b7 * h ^ 38
    - (261213880320 : F) * a5 ^ 2 * b1 * h ^ 44
    - (2889611366400 : F) * a4 ^ 5 * a5 * h ^ 30
    + (3467533639680 : F) * a4 ^ 4 * a5 * b8 * h ^ 26
    - (5201300459520 : F) * a3 * a4 ^ 3 * a5 * h ^ 35 * lambda
    + (10553363251200 : F) * a2 * a4 ^ 3 * a5 * h ^ 36
    - (2713721978880 : F) * a4 ^ 3 * a5 * b6 * h ^ 32
    + (15830044876800 : F) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 36
    - (9498026926080 : F) * a3 * a4 ^ 2 * a5 * b7 * h ^ 32
    - (10854887915520 : F) * a2 * a4 ^ 2 * a5 * b8 * h ^ 32
    + (4070582968320 : F) * a1 * a4 ^ 2 * a5 * h ^ 41 * lambda
    - (6385228185600 : F) * a0 * a4 ^ 2 * a5 * h ^ 42
    + (1915568455680 : F) * a4 ^ 2 * a5 * b4 * h ^ 38
    - (10854887915520 : F) * a3 ^ 2 * a4 * a5 * b8 * h ^ 32
    + (8141165936640 : F) * a2 * a3 * a4 * a5 * h ^ 41 * lambda
    - (12770456371200 : F) * a1 * a3 * a4 * a5 * h ^ 42
    + (4788921139200 : F) * a3 * a4 * a5 * b5 * h ^ 38
    - (6385228185600 : F) * a2 ^ 2 * a4 * a5 * h ^ 42
    + (5746705367040 : F) * a2 * a4 * a5 * b6 * h ^ 38
    + (6704489594880 : F) * a1 * a4 * a5 * b7 * h ^ 38
    + (7662273822720 : F) * a0 * a4 * a5 * b8 * h ^ 38
    - (1044855521280 : F) * a4 * a5 * b2 * h ^ 44
    + (1356860989440 : F) * a3 ^ 3 * a5 * h ^ 41 * lambda
    - (6385228185600 : F) * a2 * a3 ^ 2 * a5 * h ^ 42
    + (2873352683520 : F) * a3 ^ 2 * a5 * b6 * h ^ 38
    + (6704489594880 : F) * a2 * a3 * a5 * b7 * h ^ 38
    + (7662273822720 : F) * a1 * a3 * a5 * b8 * h ^ 38
    - (2873352683520 : F) * a0 * a3 * a5 * h ^ 47 * lambda
    - (1567283281920 : F) * a3 * a5 * b3 * h ^ 44
    + (3831136911360 : F) * a2 ^ 2 * a5 * b8 * h ^ 38
    - (2873352683520 : F) * a1 * a2 * a5 * h ^ 47 * lambda
    + (1741425868800 : F) * a0 * a2 * a5 * h ^ 48
    - (2089711042560 : F) * a2 * a5 * b4 * h ^ 44
    + (870712934400 : F) * a1 ^ 2 * a5 * h ^ 48
    - (2612138803200 : F) * a1 * a5 * b5 * h ^ 44
    - (3134566563840 : F) * a0 * a5 * b6 * h ^ 44
    - (260065022976 : F) * a4 ^ 5 * h ^ 35 * lambda
    + (4334417049600 : F) * a3 * a4 ^ 4 * h ^ 36
    - (791502243840 : F) * a4 ^ 4 * b7 * h ^ 32
    - (3618295971840 : F) * a3 * a4 ^ 3 * b8 * h ^ 32
    + (1356860989440 : F) * a2 * a4 ^ 3 * h ^ 41 * lambda
    - (4522869964800 : F) * a1 * a4 ^ 3 * h ^ 42
    + (798153523200 : F) * a4 ^ 3 * b5 * h ^ 38
    + (2035291484160 : F) * a3 ^ 2 * a4 ^ 2 * h ^ 41 * lambda
    - (13568609894400 : F) * a2 * a3 * a4 ^ 2 * h ^ 42
    + (2873352683520 : F) * a3 * a4 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F) * a2 * a4 ^ 2 * b7 * h ^ 38
    + (3831136911360 : F) * a1 * a4 ^ 2 * b8 * h ^ 38
    - (1436676341760 : F) * a0 * a4 ^ 2 * h ^ 47 * lambda
    - (783641640960 : F) * a4 ^ 2 * b3 * h ^ 44
    - (4522869964800 : F) * a3 ^ 3 * a4 * h ^ 42
    + (3352244797440 : F) * a3 ^ 2 * a4 * b7 * h ^ 38
    + (7662273822720 : F) * a2 * a3 * a4 * b8 * h ^ 38
    - (2873352683520 : F) * a1 * a3 * a4 * h ^ 47 * lambda
    + (9577842278400 : F) * a0 * a3 * a4 * h ^ 48
    - (2089711042560 : F) * a3 * a4 * b4 * h ^ 44
    - (1436676341760 : F) * a2 ^ 2 * a4 * h ^ 47 * lambda
    + (9577842278400 : F) * a1 * a2 * a4 * h ^ 48
    - (2612138803200 : F) * a2 * a4 * b5 * h ^ 44
    - (3134566563840 : F) * a1 * a4 * b6 * h ^ 44
    - (3656994324480 : F) * a0 * a4 * b7 * h ^ 44
    + (626913312768 : F) * a4 * b1 * h ^ 50
    + (1277045637120 : F) * a3 ^ 3 * b8 * h ^ 38
    - (1436676341760 : F) * a2 * a3 ^ 2 * h ^ 47 * lambda
    + (4788921139200 : F) * a1 * a3 ^ 2 * h ^ 48
    - (1306069401600 : F) * a3 ^ 2 * b5 * h ^ 44
    + (4788921139200 : F) * a2 ^ 2 * a3 * h ^ 48
    - (3134566563840 : F) * a2 * a3 * b6 * h ^ 44
    - (3656994324480 : F) * a1 * a3 * b7 * h ^ 44
    - (4179422085120 : F) * a0 * a3 * b8 * h ^ 44
    + (1253826625536 : F) * a3 * b2 * h ^ 50
    - (1828497162240 : F) * a2 ^ 2 * b7 * h ^ 44
    - (4179422085120 : F) * a1 * a2 * b8 * h ^ 44
    + (1567283281920 : F) * a0 * a2 * h ^ 53 * lambda
    + (1880739938304 : F) * a2 * b3 * h ^ 50
    + (783641640960 : F) * a1 ^ 2 * h ^ 53 * lambda
    - (5224277606400 : F) * a0 * a1 * h ^ 54
    + (2507653251072 : F) * a1 * b4 * h ^ 50
    + (3134566563840 : F) * a0 * b5 * h ^ 50 := by
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
  have h3761479876608 : (3761479876608 : F) ≠ 0 := by norm_num
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
  simp only [bridgeKappaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hW, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h32,
    h36, h54, h64, h72, h81, h144, h216, h243, h256, h324, h432, h648,
    h729, h1296, h7776, h11664, h31104, h46656, h93312, h186624, h5038848,
    h3761479876608, hh10, hh15, hh20, hh25, hh30, hh35, hh40, hh45, hh50,
    hh55]
  ring


end BridgeKappaDepression610

/-! ## Degree-`6` and degree-`4` depressed differential rows -/

section BridgeKappaDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`6` Jacobian coefficient is
exactly `7 Q E' + 6 R D' + 5 S C' + 4 T B' + 3 U A' - D R' - 2 C S'
- 3 B T' - 4 A U' - 6 W'`. -/
theorem differentialJacobian_coeff_6_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 6 =
      (7 : F) * g.coeff 7 * d (f.coeff 0) +
        (6 : F) * g.coeff 6 * d (f.coeff 1) +
        (5 : F) * g.coeff 5 * d (f.coeff 2) +
        (4 : F) * g.coeff 4 * d (f.coeff 3) +
        (3 : F) * g.coeff 3 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 6) -
          (2 : F) * f.coeff 2 * d (g.coeff 5) -
          (3 : F) * f.coeff 3 * d (g.coeff 4) -
          (4 : F) * f.coeff 4 * d (g.coeff 3) -
          (6 : F) * d (g.coeff 1) := by
  have hfd_high : ∀ n, 5 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf5]
    · have : 6 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq6 | hlt6
      · subst n
        simpa [hf6, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 6 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 6 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem08 : ((0, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 6 =
        (7 : F) * g.coeff 7 * d (f.coeff 0) +
          (6 : F) * g.coeff 6 * d (f.coeff 1) +
          (5 : F) * g.coeff 5 * d (f.coeff 2) +
          (4 : F) * g.coeff 4 * d (f.coeff 3) +
          (3 : F) * g.coeff 3 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne08_26 : ((0, 6) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne08_35 : ((0, 6) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne08_44 : ((0, 6) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne17_26 : ((1, 5) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne17_35 : ((1, 5) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne17_44 : ((1, 5) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne26_35 : ((2, 4) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne26_44 : ((2, 4) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hne35_44 : ((3, 3) : ℕ × ℕ) ≠ (4, 2) := by decide
    have hsubset :
        ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne08
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne17
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne26
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne35
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne44
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 2 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder6, hder5, hder4, hder3, hder2]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 6 =
        (1 : F) * f.coeff 1 * d (g.coeff 6) +
          (2 : F) * f.coeff 2 * d (g.coeff 5) +
          (3 : F) * f.coeff 3 * d (g.coeff 4) +
          (4 : F) * f.coeff 4 * d (g.coeff 3) +
          (6 : F) * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne08_26 : ((0, 6) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne08_35 : ((0, 6) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne08_53 : ((0, 6) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne17_26 : ((1, 5) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne17_35 : ((1, 5) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne17_53 : ((1, 5) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne26_35 : ((2, 4) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne26_53 : ((2, 4) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hne35_53 : ((3, 3) : ℕ × ℕ) ≠ (5, 1) := by decide
    have hsubset : ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne08
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne17
            ext
            · exact h1
            · omega
          have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne26
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne35
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne53
            ext
            · exact h5
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (2, 4), (3, 3), (5, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 1 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_53]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_53]),
        Finset.sum_insert (by simp [hne26_35, hne26_53]),
        Finset.sum_insert (by simp [hne35_53]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


set_option maxHeartbeats 16000000 in
theorem bridgeThetaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 W0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (hrow : (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - (1 : F) * D0 * d R -
        (2 : F) * C0 * d S0 - (3 : F) * B * d T0 -
        (4 : F) * A * d U0 - (6 : F) * d W0 = 0) :
    d (bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0 := by
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
  have hWderiv : d W0 = (7 / 6 : F) * Q * d E0 + R * d D0 +
      (5 / 6 : F) * S0 * d C0 + (2 / 3 : F) * T0 * d B +
      (1 / 2 : F) * U0 * d A - (1 / 6 : F) * D0 * d R -
      (1 / 3 : F) * C0 * d S0 - (1 / 2 : F) * B * d T0 -
      (2 / 3 : F) * A * d U0 := by
    linear_combination (-1 / 6 : F) * hrow
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h59 : d (5 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h5]
  have h89 : d (8 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h8]
  have h2027 : d (20 / 27 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h27, h20]
  simp [bridgeThetaResidual610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610, map_sub, map_add, Derivation.leibniz, smul_eq_mul,
    h2, h3, h4, h5, h6, h7, h8, h9, h12, h23, h53, h32, h43, h76, h56c,
    h109, h49, h772, h581, h736, h1027, h572, h527, h427, h351296,
    h20243, h38, h34, h316, h3128, h116, h29, h59, h89, h2027, hL, hsq,
    hsqB, hsqC, hcub, hcubB, hquar, pow_two, pow_three]
  simp [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv]
  simp [Derivation.leibniz_inv, Derivation.leibniz_div, h2, h16, h12,
    h116]
  ring


/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`4` Jacobian coefficient is
exactly `5 S E' + 4 T D' + 3 U C' + 2 V B' + W A' - D T' - 2 C U'
- 3 B V' - 4 A W'`. -/
theorem differentialJacobian_coeff_4_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 4 =
      (5 : F) * g.coeff 5 * d (f.coeff 0) +
        (4 : F) * g.coeff 4 * d (f.coeff 1) +
        (3 : F) * g.coeff 3 * d (f.coeff 2) +
        (2 : F) * g.coeff 2 * d (f.coeff 3) +
        (1 : F) * g.coeff 1 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 3) -
          (3 : F) * f.coeff 3 * d (g.coeff 2) -
          (4 : F) * f.coeff 4 * d (g.coeff 1) := by
  have hfd_high : ∀ n, 5 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf5]
    · have : 6 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq6 | hlt6
      · subst n
        simpa [hf6, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 6 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 6 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem04 : ((0, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem13 : ((1, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem22 : ((2, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem31 : ((3, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem40 : ((4, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 4 =
        (5 : F) * g.coeff 5 * d (f.coeff 0) +
          (4 : F) * g.coeff 4 * d (f.coeff 1) +
          (3 : F) * g.coeff 3 * d (f.coeff 2) +
          (2 : F) * g.coeff 2 * d (f.coeff 3) +
          (1 : F) * g.coeff 1 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne04_22 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne04_40 : ((0, 4) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne13_22 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne13_40 : ((1, 3) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne22_31 : ((2, 2) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne22_40 : ((2, 2) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hne31_40 : ((3, 1) : ℕ × ℕ) ≠ (4, 0) := by decide
    have hsubset :
        ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem22
      · subst b; exact hmem31
      · subst b; exact hmem40
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 4 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne04 : b ≠ (0, 4) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne13 : b ≠ (1, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne22 : b ≠ (2, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne31 : b ≠ (3, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne40 : b ≠ (4, 0) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne04
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne13
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne22
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne31
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne40
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31, hne04_40]),
        Finset.sum_insert (by simp [hne13_22, hne13_31, hne13_40]),
        Finset.sum_insert (by simp [hne22_31, hne22_40]),
        Finset.sum_insert (by simp [hne31_40]), Finset.sum_singleton]
      ring
    have hder4g : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder4g, hder3g, hder2g, hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 4 =
        (1 : F) * f.coeff 1 * d (g.coeff 4) +
          (2 : F) * f.coeff 2 * d (g.coeff 3) +
          (3 : F) * f.coeff 3 * d (g.coeff 2) +
          (4 : F) * f.coeff 4 * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul]
    have hne04_13 : ((0, 4) : ℕ × ℕ) ≠ (1, 3) := by decide
    have hne04_22 : ((0, 4) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne04_31 : ((0, 4) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne13_22 : ((1, 3) : ℕ × ℕ) ≠ (2, 2) := by decide
    have hne13_31 : ((1, 3) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hne22_31 : ((2, 2) : ℕ × ℕ) ≠ (3, 1) := by decide
    have hsubset : ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (4 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem04
      · subst b; exact hmem13
      · subst b; exact hmem22
      · subst b; exact hmem31
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (4 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 4 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne04 : b ≠ (0, 4) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne13 : b ≠ (1, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne22 : b ≠ (2, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne31 : b ≠ (3, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne04
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne13
            ext
            · exact h1
            · omega
          have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne22
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne31
            ext
            · exact h3
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 4), (1, 3), (2, 2), (3, 1)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 1 := by
      rw [Finset.sum_insert (by simp [hne04_13, hne04_22, hne04_31]),
        Finset.sum_insert (by simp [hne13_22, hne13_31]),
        Finset.sum_insert (by simp [hne22_31]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder0, hder1, hder2, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


set_option maxHeartbeats 80000000 in
theorem bridgeKappaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F)
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
    (hrow : (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        (1 : F) * W0 * d A - (1 : F) * D0 * d T0 -
        (2 : F) * C0 * d U0 - (3 : F) * B * d V0 -
        (4 : F) * A * d W0 = 0) :
    d (bridgeKappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
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
  have hrow_red := hrow
  simp only [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow_red
  simp only [bridgeKappaResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h16f, h13, h12, h18f, h23, h29, h56c, h351296, h536,
    h572, h20243, h427, h827, h481, h49, h38531104, h35432, h736, h772,
    h3256, h332, h964, h316, h38, h34, h35729, h2081, h1027, h527, h109,
    hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
    hsq, hsqB, hsqC, hsqD, hcub, hcubB, hquar, hquint, pow_two,
    pow_three, zero_mul, add_zero, mul_zero]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610, pow_two, pow_three]
  linear_combination (1 / 6 : F) * hrow_red


end BridgeKappaDepressedRows610

/-! ## Affine depression of a degree-ten source, `z¹` coefficient -/

section BridgeKappaAffineDecic610

variable {k : Type*} [Field k] [CharZero k]


theorem affineDepress_degreeTen_coeff1_610_bridge
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 1 =
      -10 * r ^ 9 + 9 * (p.coeff 9 / h ^ 9) * r ^ 8 -
        8 * (p.coeff 8 / h ^ 8) * r ^ 7 +
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 -
        6 * (p.coeff 6 / h ^ 6) * r ^ 5 +
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 -
        4 * (p.coeff 4 / h ^ 4) * r ^ 3 +
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 -
        2 * (p.coeff 2 / h ^ 2) * r + p.coeff 1 / h := by
  let plow : (RatFunc k)[X] :=
    p - Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 - Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 -
      Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 - Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 -
      Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 - Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 -
      Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 - Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 -
      Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 - Polynomial.C (p.coeff 1) * Polynomial.X ^ 1
  have hplow : ∀ n, 1 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h1 | hlt1
    · subst n; simp
    · have : 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h2 | hlt2
      · subst n; simp
      · have : 3 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h3 | hlt3
        · subst n; simp
        · have : 4 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h4 | hlt4
          · subst n; simp
          · have : 5 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h5 | hlt5
            · subst n; simp
            · have : 6 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h6 | hlt6
              · subst n; simp
              · have : 7 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h7 | hlt7
                · subst n; simp
                · have : 8 ≤ n := by omega
                  rcases Nat.eq_or_lt_of_le this with h8 | hlt8
                  · subst n; simp
                  · have : 9 ≤ n := by omega
                    rcases Nat.eq_or_lt_of_le this with h9 | hlt9
                    · subst n; simp
                    · have : 10 ≤ n := by omega
                      rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                      · subst n; simp [hp10]
                      · simp [hp_high n (by omega), show n ≠ 10 by omega,
                          show n ≠ 9 by omega, show n ≠ 8 by omega,
                          show n ≠ 7 by omega, show n ≠ 6 by omega,
                          show n ≠ 5 by omega, show n ≠ 4 by omega,
                          show n ≠ 3 by omega, show n ≠ 2 by omega,
                          show n ≠ 1 by omega]
  have hplowDeg : plow.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 + Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 +
        Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 + Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 +
        Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 + Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 +
        Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 + Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 +
        Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X ^ 1 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := rfl
    have hsum (A B D E G H I J K M s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + M + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + M.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + M + s).comp t =
          (A + B + D + E + G + H + I + J + K + M).comp t + s.comp t :=
        Polynomial.add_comp
      have h2 : (A + B + D + E + G + H + I + J + K + M).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + M.comp t :=
        Polynomial.add_comp
      have h3 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t :=
        Polynomial.add_comp
      have h4 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t :=
        Polynomial.add_comp
      have h5 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t :=
        Polynomial.add_comp
      have h6 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := Polynomial.add_comp
      have h7 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := Polynomial.add_comp
      have h8 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := Polynomial.add_comp
      have h9 : (A + B + D).comp t =
          (A + B).comp t + D.comp t := Polynomial.add_comp
      have h10 : (A + B).comp t = A.comp t + B.comp t := Polynomial.add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    exact hdef.trans ((congrArg (fun t => t.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 1 ≤ n) :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤
          plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree ≤ 0 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤ 0 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 1 ≤ n))
  have h10_1 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -10 * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 1 hh]
    have hle : (1 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 1 = 10 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]; ring
  have h9_1 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        9 * (p.coeff 9 / h ^ 9) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 1 hh]
    have hle : (1 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 1 = 9 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h8_1 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -8 * (p.coeff 8 / h ^ 8) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 1 hh]
    have hle : (1 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 1 = 8 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h7_1 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 1 hh]
    have hle : (1 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 1 = 7 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h6_1 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -6 * (p.coeff 6 / h ^ 6) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 1 hh]
    have hle : (1 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 1 = 6 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h5_1 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 1 hh]
    have hle : (1 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 1 = 5 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h4_1 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -4 * (p.coeff 4 / h ^ 4) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 1 hh]
    have hle : (1 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 1 = 4 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]; ring
  have h3_1 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 1 hh]
    have hle : (1 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 1 = 3 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]; ring
  have h2_1 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        -2 * (p.coeff 2 / h ^ 2) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 1 hh]
    have hle : (1 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 1 = 2 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]; ring
  have h1_1 :
      ((Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 1 =
        p.coeff 1 / h := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 1 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, h10_1, h9_1, h8_1, h7_1, h6_1, h5_1, h4_1, h3_1,
    h2_1, h1_1, hlow 1 (by omega)]
  ring


end BridgeKappaAffineDecic610

/-! ## Weight-`55` power relation on the literal source -/

section BridgeKappaPowerRelation610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The tenth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁵⁵`.  The degree-`5` iota
integral and the exact `18 q₀ h⁵⁰` residual remain available from the
ninth packet. -/
theorem nonzeroFace610_bridgeKappaPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ mu : k,
      bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C mu * h0 ^ 55 := by
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
  have hkappa0deriv :
      ratFuncDerivation68
        (bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    bridgeKappaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) hLconst halpha0 hbeta0
      hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv htheta0deriv
      (by simpa using hrow6) (by simpa using hrow4)
  obtain ⟨mu0, hmu0⟩ :
      ∃ a : k,
        bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hkappa0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (3761479876608 : RatFunc k) * hRF ^ 55 *
          bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := bridgeKappaDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [bridgeClearedKappaDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, b1, bridgeKappaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, zetaResidual610, etaResidual610,
      bridgeThetaResidual610, hf4, hf3, hf2, hf1, hf0, hg1, hg2, hg3, hg4, hg5,
      hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (3761479876608 * mu0) * h0 ^ 55) := by
    rw [hclear, hmu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨3761479876608 * mu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end BridgeKappaPowerRelation610

/-! ## Jet head and tail of the cleared `κ` defect -/

section BridgeKappaJet610

variable {R : Type*} [CommRing R]

/-- Order-`48` head of the jet-substituted cleared `κ` defect: the
coefficient of `h⁴⁸` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `bridgeClearedKappaDefect610`,
kept in its fully factored form. -/
def bridgeKappaJetHead610 (a41 p31 s1 u1 q52 q4 : R) : R :=
  (4837294080 : R) * p31 *
    ((264 : R) * p31 ^ 2 * s1 + (693 : R) * a41 * p31 * u1 -
      (935 : R) * a41 * p31 ^ 2 - (432 : R) * a41 * q4 -
      (270 : R) * p31 * q52)

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `κ` defect above order `h⁴⁹`. -/
def bridgeKappaJetTail610
    (hh w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 lam : R) : R :=
    (1884529152000 : R) * w1 ^ 2 * p31 ^ 3
    - (4749013463040 : R) * w1 ^ 2 * p31 ^ 2 * u1
    + (1915568455680 : R) * w1 ^ 2 * p31 * q4
    + (15830044876800 : R) * w1 * a41 ^ 2 * p31 ^ 2
    - (9498026926080 : R) * w1 * a41 ^ 2 * p31 * u1
    + (1915568455680 : R) * w1 * a41 ^ 2 * q4
    - (10854887915520 : R) * w1 * a41 * p31 ^ 2 * s1
    + (4788921139200 : R) * w1 * a41 * p31 * q52
    + (2873352683520 : R) * w1 * p31 ^ 2 * b62
    - (6385228185600 : R) * w1 * p31 ^ 2 * p2
    + (6704489594880 : R) * w1 * p31 * u1 * p2
    - (2089711042560 : R) * w1 * p2 * q4
    + (4334417049600 : R) * a41 ^ 4 * p31
    - (791502243840 : R) * a41 ^ 4 * u1
    - (3618295971840 : R) * a41 ^ 3 * p31 * s1
    + (798153523200 : R) * a41 ^ 3 * q52
    + (2873352683520 : R) * a41 ^ 2 * p31 * b62
    - (13568609894400 : R) * a41 ^ 2 * p31 * p2
    + (3352244797440 : R) * a41 ^ 2 * u1 * p2
    + (7662273822720 : R) * a41 * p31 * s1 * p2
    - (2612138803200 : R) * a41 * q52 * p2
    - (3134566563840 : R) * p31 * b62 * p2
    + (4788921139200 : R) * p31 * p2 ^ 2
    - (1828497162240 : R) * u1 * p2 ^ 2
    + (1356860989440 : R) * lam * w1 * p31 ^ 3
    + (2035291484160 : R) * lam * a41 ^ 2 * p31 ^ 2
    - (1436676341760 : R) * lam * p31 ^ 2 * p2
    - (2889611366400 : R) * hh * w1 ^ 3 * a41 * p31 ^ 2
    + (12136367738880 : R) * hh * w1 ^ 3 * a41 * p31 * u1
    - (1809147985920 : R) * hh * w1 ^ 3 * a41 * q4
    + (6935067279360 : R) * hh * w1 ^ 3 * p31 ^ 2 * s1
    - (2261434982400 : R) * hh * w1 ^ 3 * p31 * q52
    - (15892862515200 : R) * hh * w1 ^ 2 * a41 ^ 3 * p31
    + (6068183869440 : R) * hh * w1 ^ 2 * a41 ^ 3 * u1
    + (20805201838080 : R) * hh * w1 ^ 2 * a41 ^ 2 * p31 * s1
    - (3392152473600 : R) * hh * w1 ^ 2 * a41 ^ 2 * q52
    - (8141165936640 : R) * hh * w1 ^ 2 * a41 * p31 * b62
    + (11307174912000 : R) * hh * w1 ^ 2 * a41 * p31 * p2
    - (9498026926080 : R) * hh * w1 ^ 2 * a41 * u1 * p2
    - (10854887915520 : R) * hh * w1 ^ 2 * p31 * s1 * p2
    + (2394460569600 : R) * hh * w1 ^ 2 * q52 * p2
    - (2889611366400 : R) * hh * w1 * a41 ^ 5
    + (3467533639680 : R) * hh * w1 * a41 ^ 4 * s1
    - (2713721978880 : R) * hh * w1 * a41 ^ 3 * b62
    + (10553363251200 : R) * hh * w1 * a41 ^ 3 * p2
    - (10854887915520 : R) * hh * w1 * a41 ^ 2 * s1 * p2
    + (5746705367040 : R) * hh * w1 * a41 * b62 * p2
    - (6385228185600 : R) * hh * w1 * a41 * p2 ^ 2
    - (1567283281920 : R) * hh * w1 * p31 * q3
    + (3831136911360 : R) * hh * w1 * s1 * p2 ^ 2
    - (783641640960 : R) * hh * a41 ^ 2 * q3
    + (4788921139200 : R) * hh * p31 ^ 2 * p1
    - (3656994324480 : R) * hh * p31 * u1 * p1
    + (1880739938304 : R) * hh * p2 * q3
    + (2507653251072 : R) * hh * p1 * q4
    - (7801950689280 : R) * hh * lam * w1 ^ 2 * a41 * p31 ^ 2
    - (5201300459520 : R) * hh * lam * w1 * a41 ^ 3 * p31
    + (8141165936640 : R) * hh * lam * w1 * a41 * p31 * p2
    - (260065022976 : R) * hh * lam * a41 ^ 5
    + (1356860989440 : R) * hh * lam * a41 ^ 3 * p2
    - (1436676341760 : R) * hh * lam * a41 * p2 ^ 2
    - (3491613734400 : R) * hh ^ 2 * w1 ^ 5 * p31 ^ 2
    - (2932955536896 : R) * hh ^ 2 * w1 ^ 5 * p31 * u1
    + (346753363968 : R) * hh ^ 2 * w1 ^ 5 * q4
    - (1745806867200 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * p31
    - (7332388842240 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * u1
    - (16759745925120 : R) * hh ^ 2 * w1 ^ 4 * a41 * p31 * s1
    + (2167208524800 : R) * hh ^ 2 * w1 ^ 4 * a41 * q52
    + (2600650229760 : R) * hh ^ 2 * w1 ^ 4 * p31 * b62
    + (5056819891200 : R) * hh ^ 2 * w1 ^ 4 * p31 * p2
    + (3034091934720 : R) * hh ^ 2 * w1 ^ 4 * u1 * p2
    + (4655484979200 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 4
    - (11173163950080 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 3 * s1
    + (5201300459520 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * b62
    - (2889611366400 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p2
    + (13870134558720 : R) * hh ^ 2 * w1 ^ 3 * a41 * s1 * p2
    - (2713721978880 : R) * hh ^ 2 * w1 ^ 3 * b62 * p2
    - (1507623321600 : R) * hh ^ 2 * w1 ^ 3 * p2 ^ 2
    + (1436676341760 : R) * hh ^ 2 * w1 ^ 2 * a41 * q3
    - (12770456371200 : R) * hh ^ 2 * w1 * a41 * p31 * p1
    + (6704489594880 : R) * hh ^ 2 * w1 * a41 * u1 * p1
    + (7662273822720 : R) * hh ^ 2 * w1 * p31 * s1 * p1
    - (2612138803200 : R) * hh ^ 2 * w1 * q52 * p1
    - (4522869964800 : R) * hh ^ 2 * a41 ^ 3 * p1
    + (3831136911360 : R) * hh ^ 2 * a41 ^ 2 * s1 * p1
    - (3134566563840 : R) * hh ^ 2 * a41 * b62 * p1
    + (9577842278400 : R) * hh ^ 2 * a41 * p2 * p1
    + (1253826625536 : R) * hh ^ 2 * p31 * q2
    - (4179422085120 : R) * hh ^ 2 * s1 * p2 * p1
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 4 * p31 ^ 2
    + (12569809443840 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 ^ 2 * p31
    - (5201300459520 : R) * hh ^ 2 * lam * w1 ^ 3 * p31 * p2
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 4
    - (7801950689280 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 2 * p2
    + (2035291484160 : R) * hh ^ 2 * lam * w1 ^ 2 * p2 ^ 2
    - (2873352683520 : R) * hh ^ 2 * lam * a41 * p31 * p1
    + (8826023606400 : R) * hh ^ 3 * w1 ^ 6 * a41 * p31
    + (2851484549760 : R) * hh ^ 3 * w1 ^ 6 * a41 * u1
    + (3258839485440 : R) * hh ^ 3 * w1 ^ 6 * p31 * s1
    - (349161373440 : R) * hh ^ 3 * w1 ^ 6 * q52
    + (2715699571200 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 3
    + (9776518456320 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 2 * s1
    - (2513961888768 : R) * hh ^ 3 * w1 ^ 5 * a41 * b62
    - (6983227468800 : R) * hh ^ 3 * w1 ^ 5 * a41 * p2
    - (3351949185024 : R) * hh ^ 3 * w1 ^ 5 * s1 * p2
    - (339215247360 : R) * hh ^ 3 * w1 ^ 4 * q3
    - (3015246643200 : R) * hh ^ 3 * w1 ^ 3 * p31 * p1
    - (3166008975360 : R) * hh ^ 3 * w1 ^ 3 * u1 * p1
    + (5653587456000 : R) * hh ^ 3 * w1 ^ 2 * a41 ^ 2 * p1
    - (10854887915520 : R) * hh ^ 3 * w1 ^ 2 * a41 * s1 * p1
    + (2873352683520 : R) * hh ^ 3 * w1 ^ 2 * b62 * p1
    + (798153523200 : R) * hh ^ 3 * w1 ^ 2 * p2 * p1
    - (1044855521280 : R) * hh ^ 3 * w1 * a41 * q2
    + (9577842278400 : R) * hh ^ 3 * a41 * p31 * p0
    - (3656994324480 : R) * hh ^ 3 * a41 * u1 * p0
    - (4179422085120 : R) * hh ^ 3 * p31 * s1 * p0
    + (3134566563840 : R) * hh ^ 3 * q52 * p0
    - (7332388842240 : R) * hh ^ 3 * lam * w1 ^ 5 * a41 * p31
    - (6110324035200 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 ^ 3
    + (6284904721920 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 * p2
    + (4070582968320 : R) * hh ^ 3 * lam * w1 ^ 2 * p31 * p1
    + (4070582968320 : R) * hh ^ 3 * lam * w1 * a41 ^ 2 * p1
    - (2873352683520 : R) * hh ^ 3 * lam * w1 * p2 * p1
    - (2071125045000 : R) * hh ^ 4 * w1 ^ 8 * p31
    - (347949007560 : R) * hh ^ 4 * w1 ^ 8 * u1
    - (5302080115200 : R) * hh ^ 4 * w1 ^ 7 * a41 ^ 2
    - (3181248069120 : R) * hh ^ 4 * w1 ^ 7 * a41 * s1
    + (349161373440 : R) * hh ^ 4 * w1 ^ 7 * b62
    + (2133763948800 : R) * hh ^ 4 * w1 ^ 7 * p2
    + (5056819891200 : R) * hh ^ 4 * w1 ^ 4 * a41 * p1
    + (3467533639680 : R) * hh ^ 4 * w1 ^ 4 * s1 * p1
    + (319261409280 : R) * hh ^ 4 * w1 ^ 3 * q2
    + (798153523200 : R) * hh ^ 4 * w1 ^ 2 * p31 * p0
    + (3352244797440 : R) * hh ^ 4 * w1 ^ 2 * u1 * p0
    - (6385228185600 : R) * hh ^ 4 * w1 * a41 ^ 2 * p0
    + (7662273822720 : R) * hh ^ 4 * w1 * a41 * s1 * p0
    - (3134566563840 : R) * hh ^ 4 * w1 * b62 * p0
    + (1741425868800 : R) * hh ^ 4 * w1 * p2 * p0
    + (870712934400 : R) * hh ^ 4 * w1 * p1 ^ 2
    + (626913312768 : R) * hh ^ 4 * a41 * q1
    + (1192968025920 : R) * hh ^ 4 * lam * w1 ^ 7 * p31
    + (4175388090720 : R) * hh ^ 4 * lam * w1 ^ 6 * a41 ^ 2
    - (1222064807040 : R) * hh ^ 4 * lam * w1 ^ 6 * p2
    - (5201300459520 : R) * hh ^ 4 * lam * w1 ^ 3 * a41 * p1
    - (2873352683520 : R) * hh ^ 4 * lam * w1 * p31 * p0
    - (1436676341760 : R) * hh ^ 4 * lam * a41 ^ 2 * p0
    + (1567283281920 : R) * hh ^ 4 * lam * p2 * p0
    + (783641640960 : R) * hh ^ 4 * lam * p1 ^ 2
    + (2018963377200 : R) * hh ^ 5 * w1 ^ 9 * a41
    + (346108007520 : R) * hh ^ 5 * w1 ^ 9 * s1
    - (2211355365120 : R) * hh ^ 5 * w1 ^ 6 * p1
    - (3015246643200 : R) * hh ^ 5 * w1 ^ 3 * a41 * p0
    - (3618295971840 : R) * hh ^ 5 * w1 ^ 3 * s1 * p0
    - (261213880320 : R) * hh ^ 5 * w1 ^ 2 * q1
    - (5224277606400 : R) * hh ^ 5 * p1 * p0
    - (1168114525380 : R) * hh ^ 5 * lam * w1 ^ 8 * a41
    + (1256980944384 : R) * hh ^ 5 * lam * w1 ^ 5 * p1
    + (4070582968320 : R) * hh ^ 5 * lam * w1 ^ 2 * a41 * p0
    - (231612681800 : R) * hh ^ 6 * w1 ^ 11
    + (2311689093120 : R) * hh ^ 6 * w1 ^ 5 * p0
    + (114648277491 : R) * hh ^ 6 * lam * w1 ^ 10
    - (1300325114880 : R) * hh ^ 6 * lam * w1 ^ 4 * p0

end BridgeKappaJet610

/-! ## Jet factorization of the cleared `κ` defect -/

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the fifteenth-face jet the cleared `κ` defect factors exactly as
`h⁴⁸` times its factored order-`48` head plus `h` times the tail. -/
theorem bridgeClearedKappaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedKappaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 48 *
        (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 +
          h * bridgeKappaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  simp only [bridgeClearedKappaDefect610, bridgeKappaJetHead610,
    bridgeKappaJetTail610]
  ring

/-- Evaluation commutes with the order-`48` head. -/
theorem bridgeKappaJetHead610_eval
    (a41 p31 s1 u1 q52 q4 : k[X]) (x : k) :
    (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4).eval x =
      bridgeKappaJetHead610 (a41.eval x) (p31.eval x) (s1.eval x)
        (u1.eval x) (q52.eval x) (q4.eval x) := by
  simp only [bridgeKappaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeKappaJetFactor610

/-! ## Scalar consequences of the vanishing order-`48` head -/

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`48` head modulo the
tenth-face root laws alone: the head reduces to the exact factored
relation `a₄₁ p₃₁³ = 0`. -/
theorem bridgeKappa_chamberFree_split610
    (a41 p31 s1 u1 q52 q4 : F)
    (hhead : bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    a41 * p31 ^ 3 = 0 := by
  simp only [bridgeKappaJetHead610] at hhead
  linear_combination (1 / 580475289600 : F) * hhead -
      (11 / 15 : F) * p31 ^ 3 * hs -
      (77 / 40 : F) * a41 * p31 ^ 2 * hu +
      (1 / 4 : F) * p31 ^ 2 * hq52 + (2 / 5 : F) * a41 * p31 * hq4

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ ≠ 0` complement child the factored root relation
forces `a₄₁ = 0`, the retained core forces `w₁ = 0`, and the two
remaining ground relations collapse to the pins `80 p₂ = 9 λ p₃₁` and
`16 b₆₂ = -5 λ p₃₁`. -/
theorem bridgeKappa_complement_pins610
    (w1 a41 p31 p2 b62 lam : F) (hnz : p31 ≠ 0)
    (hzero : a41 * p31 ^ 3 = 0)
    (hcore : (5 : F) * a41 ^ 2 + (2 : F) * p31 * w1 = 0)
    (hp2n : (80 : F) * p2 - (9 : F) * lam * p31 -
      (8 : F) * p31 * w1 = 0)
    (hb62n : (144 : F) * b62 + (45 : F) * lam * p31 -
      (152 : F) * p31 * w1 = 0) :
    a41 = 0 ∧ w1 = 0 ∧ (80 : F) * p2 = (9 : F) * lam * p31 ∧
      (16 : F) * b62 = -(5 : F) * lam * p31 := by
  have ha : a41 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (pow_ne_zero 3 hnz)
  have hpw : p31 * w1 = 0 := by
    linear_combination (1 / 2 : F) * hcore - (5 / 2 : F) * a41 * ha
  have hw : w1 = 0 := by
    rcases mul_eq_zero.mp hpw with h | h
    · exact absurd h hnz
    · exact h
  refine ⟨ha, hw, ?_, ?_⟩
  · linear_combination hp2n + (8 : F) * p31 * hw
  · linear_combination (1 / 9 : F) * hb62n + (152 / 9 : F) * p31 * hw

end BridgeKappaScalars610

/-! ## Finite local kappa integral bridge packet -/

section NonzeroKappaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `κ` integral bridge: the terminal integral closure
packet (the `ι` packet reused opaquely) together with the imported
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0`, and the four-children combination — the three
`p₃₁(a) = 0` children are retained unchanged (the head carries an
overall `p₃₁` factor there), while the `p₃₁(a) ≠ 0` child is refined
to `a₄₁(a) = 0`, `w₁(a) = 0` and the pins `80 p₂(a) = 9 λ p₃₁(a)`,
`16 b₆₂(a) = -5 λ p₃₁(a)`, with `ψ₂(a) = -209952 λ p₁(a)` collapsing
the retained boundary elimination into the Keller row.  No child is
closed. -/
theorem nonzeroFace610_linearRoot_kappaIntegralBridge
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
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]) (iotaK kappaMu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (3 : k) * u1.eval a = (5 : k) * p31.eval a ∧
        (9 : k) * q52.eval a =
          (10 : k) * a41.eval a * p31.eval a ∧
        (9 : k) * (q.coeff 4).eval a = (5 : k) * (p31.eval a) ^ 2 ∧
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
        (p31.eval a) ^ 2 * ((27 : k) * b62.eval a -
            (30 : k) * (a41.eval a) ^ 2 - (5 : k) * (p.coeff 2).eval a +
            (9 : k) * lambda * p31.eval a -
            (40 : k) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : k) * b62.eval a -
            (170 : k) * (a41.eval a) ^ 2 +
            (45 : k) * lambda * p31.eval a -
            (220 : k) * p31.eval a * w1.eval a) = 0 ∧
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
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : k[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : k) * u2.eval a - (30 : k) * p32.eval a -
                    (20 : k) * a41.eval a * w1.eval a +
                  (9 : k) * lambda * a41.eval a = 0 ∧
                (81 : k) * q41.eval a -
                    (90 : k) * a41.eval a * (p.coeff 2).eval a +
                  (5 : k) * (a41.eval a) ^ 3 = 0 ∧
                (216 : k) * q53.eval a +
                    (27 : k) * lambda * (a41.eval a) ^ 2 +
                  (40 : k) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : k) * a41.eval a * p32.eval a +
                  (108 : k) * lambda * (p.coeff 2).eval a -
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : k) * (q.coeff 3).eval a -
                    (81 : k) * lambda * (a41.eval a) ^ 3 -
                  (320 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : k) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : k) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : k) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : k) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : k) * (a41.eval a) ^ 4 -
                      (35 : k) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : k) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : k) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : k) * b62.eval a -
                  (5 : k) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : k) * (p.coeff 2).eval a =
                  (9 : k) * lambda * p31.eval a ∧
                (16 : k) * b62.eval a =
                  -(5 : k) * lambda * p31.eval a ∧
                ∃ (omega psi psi2 : k[X]),
                  (583200 : k[X]) * p31 ^ 2 -
                      (489888 : k[X]) * p31 * u1 +
                    (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
                  omega.eval a =
                    (648 : k) * a41.eval a *
                      ((80 : k) * (a41.eval a) ^ 2 +
                          (297 : k) * lambda * p31.eval a -
                        (960 : k) * p31.eval a * w1.eval a) ∧
                  omega + (-(518400 : k[X]) * a41 ^ 3 +
                      (466560 : k[X]) * a41 ^ 2 * s1 -
                      (419904 : k[X]) * a41 * b62 -
                      (349920 : k[X]) * a41 * Polynomial.C lambda *
                        p31 +
                      (1166400 : k[X]) * a41 * p.coeff 2 -
                      (1360800 : k[X]) * a41 * p31 * w1 +
                      (816480 : k[X]) * a41 * u1 * w1 -
                      (559872 : k[X]) * p.coeff 2 * s1 +
                      (933120 : k[X]) * p31 * s1 * w1 -
                      (349920 : k[X]) * q52 * w1) = h0 * psi ∧
                  psi.eval a =
                    (162 : k) * w1.eval a *
                      ((7600 : k) * (a41.eval a) ^ 2 * w1.eval a -
                          (2520 : k) * lambda * (a41.eval a) ^ 2 +
                          (243 : k) * lambda ^ 2 * p31.eval a -
                          (1980 : k) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : k) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : k[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : k[X]) * b62 * w1 ^ 2 -
                    (349920 : k[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : k[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : k[X]) * p31 * w1 ^ 3 -
                    (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : k) * ((1980 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : k) * lambda * (p.coeff 1).eval a -
                      (405 : k) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  psi2.eval a =
                    -(209952 : k) * lambda * (p.coeff 1).eval a ∧
                  (288 : k) * ((729 : k) * lambda +
                        (405 : k) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - j) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : k) * ((1980 : k) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : k) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs, hu,
    hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hipow,
    hipeel, hiheadeval, hires1, hires2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralClosure p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨kappaMu, hkpow⟩ :=
    nonzeroFace610_bridgeKappaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hkpowJet :
      bridgeClearedKappaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C kappaMu * h0 ^ 55 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hkpow
  have hkpeel :
      bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
          h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C kappaMu * h0 ^ 7 := by
    have h48 : (h0 : k[X]) ^ 48 ≠ 0 := pow_ne_zero 48 hh0
    apply mul_left_cancel₀ h48
    rw [← bridgeClearedKappaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hkpowJet]
    ring
  have hkheadeval :
      bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
        (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hkpeel
    have h7z : (0 : k) ^ 7 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeKappaJetHead610_eval, h7z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hksplit0 : a41.eval a * (p31.eval a) ^ 3 = 0 :=
    bridgeKappa_chamberFree_split610 (a41.eval a) (p31.eval a)
      (s1.eval a) (u1.eval a) (q52.eval a) ((q.coeff 4).eval a)
      hkheadeval hMs hTu hVq hWq
  have hksplit : a41.eval a = 0 ∨ p31.eval a = 0 := by
    rcases mul_eq_zero.mp hksplit0 with h | h
    · exact Or.inl h
    · right
      by_contra hne
      exact pow_ne_zero 3 hne h
  refine ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, hires1, hires2, hkpow,
    hkpeel, hkheadeval, hksplit0, hksplit, ?_⟩
  rcases halt with hleft | ⟨hload1, hload2, hcd⟩
  · exact Or.inl hleft
  · rcases hcd with ⟨hz, hp2pin, hb62pin⟩ | ⟨hnz, hcore, hp2n, hb62n,
      omega, psi, psi2, homega, homegaval, hpsieq, hpsival, hpsi2eq,
      hpsi2val, heli2⟩
    · exact Or.inr ⟨hload1, hload2, Or.inl ⟨hz, hp2pin, hb62pin⟩⟩
    · obtain ⟨ha41z, hw1z, hp2k, hb62k⟩ :=
        bridgeKappa_complement_pins610 (w1.eval a) (a41.eval a)
          (p31.eval a) ((p.coeff 2).eval a) (b62.eval a) lambda hnz
          hksplit0 hcore hp2n hb62n
      have hpsi2k : psi2.eval a =
          -(209952 : k) * lambda * (p.coeff 1).eval a := by
        rw [hpsi2val, ha41z, hw1z]
        ring
      exact Or.inr ⟨hload1, hload2, Or.inr ⟨hnz, ha41z, hw1z, hp2k,
        hb62k, omega, psi, psi2, homega, homegaval, hpsieq, hpsival,
        hpsi2eq, hpsi2val, hpsi2k, heli2⟩⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing `κ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the terminal integral closure packet with the
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0` (honestly `a₄₁(a) = 0 ∨ p₃₁(a) = 0`), and the
refined `p₃₁(a) ≠ 0` child carrying `a₄₁(a) = 0`, `w₁(a) = 0`, the
pins `80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)` and the
collapsed `ψ₂(a) = -209952 λ p₁(a)`.  The ground constants `iotaK` and
`kappaMu` are preserved, not cleared, and no child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu : K)
      (w1 a41 s1 u1 p31 b62 q52 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (3 : K) * u1.eval a = (5 : K) * p31.eval a ∧
        (9 : K) * q52.eval a =
          (10 : K) * a41.eval a * p31.eval a ∧
        (9 : K) * (q.coeff 4).eval a = (5 : K) * (p31.eval a) ^ 2 ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
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
        (p31.eval a) ^ 2 * ((27 : K) * b62.eval a -
            (30 : K) * (a41.eval a) ^ 2 - (5 : K) * (p.coeff 2).eval a +
            (9 : K) * lambda * p31.eval a -
            (40 : K) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : K) * b62.eval a -
            (170 : K) * (a41.eval a) ^ 2 +
            (45 : K) * lambda * p31.eval a -
            (220 : K) * p31.eval a * w1.eval a) = 0 ∧
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
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : K[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : K) * u2.eval a - (30 : K) * p32.eval a -
                    (20 : K) * a41.eval a * w1.eval a +
                  (9 : K) * lambda * a41.eval a = 0 ∧
                (81 : K) * q41.eval a -
                    (90 : K) * a41.eval a * (p.coeff 2).eval a +
                  (5 : K) * (a41.eval a) ^ 3 = 0 ∧
                (216 : K) * q53.eval a +
                    (27 : K) * lambda * (a41.eval a) ^ 2 +
                  (40 : K) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : K) * a41.eval a * p32.eval a +
                  (108 : K) * lambda * (p.coeff 2).eval a -
                    (240 : K) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : K) * (q.coeff 3).eval a -
                    (81 : K) * lambda * (a41.eval a) ^ 3 -
                  (320 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : K) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : K) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : K) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : K) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : K) * (a41.eval a) ^ 4 -
                      (35 : K) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : K) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : K) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : K) * b62.eval a -
                  (5 : K) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : K) * (p.coeff 2).eval a =
                  (9 : K) * lambda * p31.eval a ∧
                (16 : K) * b62.eval a =
                  -(5 : K) * lambda * p31.eval a ∧
                ∃ (omega psi psi2 : K[X]),
                  (583200 : K[X]) * p31 ^ 2 -
                      (489888 : K[X]) * p31 * u1 +
                    (419904 : K[X]) * q.coeff 4 = h0 * omega ∧
                  omega.eval a =
                    (648 : K) * a41.eval a *
                      ((80 : K) * (a41.eval a) ^ 2 +
                          (297 : K) * lambda * p31.eval a -
                        (960 : K) * p31.eval a * w1.eval a) ∧
                  omega + (-(518400 : K[X]) * a41 ^ 3 +
                      (466560 : K[X]) * a41 ^ 2 * s1 -
                      (419904 : K[X]) * a41 * b62 -
                      (349920 : K[X]) * a41 * Polynomial.C lambda *
                        p31 +
                      (1166400 : K[X]) * a41 * p.coeff 2 -
                      (1360800 : K[X]) * a41 * p31 * w1 +
                      (816480 : K[X]) * a41 * u1 * w1 -
                      (559872 : K[X]) * p.coeff 2 * s1 +
                      (933120 : K[X]) * p31 * s1 * w1 -
                      (349920 : K[X]) * q52 * w1) = h0 * psi ∧
                  psi.eval a =
                    (162 : K) * w1.eval a *
                      ((7600 : K) * (a41.eval a) ^ 2 * w1.eval a -
                          (2520 : K) * lambda * (a41.eval a) ^ 2 +
                          (243 : K) * lambda ^ 2 * p31.eval a -
                          (1980 : K) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : K) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : K[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : K[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : K[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : K[X]) * b62 * w1 ^ 2 -
                    (349920 : K[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : K[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : K[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : K[X]) * p31 * w1 ^ 3 -
                    (362880 : K[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : K) * ((1980 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : K) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : K) * lambda * (p.coeff 1).eval a -
                      (405 : K) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  psi2.eval a =
                    -(209952 : K) * lambda * (p.coeff 1).eval a ∧
                  (288 : K) * ((729 : K) * lambda +
                        (405 : K) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - jK) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : K) * ((1980 : K) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : K) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) ∧
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', iotaK, kappaMu, hwN,
    ha4sN, hp3N, hsN, huN, hb6sN, hq5N, hMs', hTu', hVq', hWq',
    hUload', hrow, hroweval, hipow, hipeel, hiheadeval, hres1, hres2,
    hkpow, hkpeel, hkheadeval, hksplit0, hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, w1', a41', s1', u1', p31',
    b62', q52', hh0, hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N,
    hsN, huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, hipow,
    hipeel, hiheadeval, hres1, hres2, hkpow, hkpeel, hkheadeval,
    hksplit0, hksplit, halt, hN'⟩

end NonzeroKappaIntegralBridge610

#print axioms nonzeroFace610_linearRoot_kappaIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge

#print axioms nonzeroFace610_bridgeKappaPowerRelation

end Max11DegreeRoutes
