import Fable610ScaleTwoFifteenthFinalRowScratch
import Grok610ScaleZeroSeventhDefectScratch

/-! # Terminal integral bridge for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the fifteenth final-row packet exhausts the Jacobian
coefficient tower: the degree-`0` row is the Keller constant
`W E' - D X' = j` and there is no unused row below it.  The remaining
mechanism on this face is clearing an isolated first integral.  Among
the uncleared degree-`5` through degree-`1` first integrals only the
degree-`5` integral `ι` admits an exact construction isolated on the
second- through eighth-face integrals `α, β, γ, δ, ε, ζ, η` — the
degree-`4` and lower integrals need the degree-`6` `θ` tower as well —
so `ι` is the lowest, most constrained choice.

This file constructs `ι` for the scale-two chain and derives its exact
literal-source `h`-adic clearing: `d ι = 0` on the depressed degree-`5`
row (`terminalIotaResidual610_deriv_zero`), `18 h⁵⁰ ι` is the explicit
weight-`50` polynomial numerator `terminalClearedIotaDefect610`, and on
the literal source the cleared defect is a ground constant times `h₀⁵⁰`
(`nonzeroFace610_terminalIotaPowerRelation`).  The `ι` ground constant
`iotaK` joins `ζ` and `η` and is not cleared to zero.

Combining the clearing with the fifteenth-face jet `p₅ = h₀⁵ w₁`,
`p₄ = h₀³ a₄₁`, `p₃ = h₀ p₃₁`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁵ u₁`,
`q₆ = h₀⁴ b₆₂`, `q₅ = h₀² q₅₂` factors the numerator through `h₀⁴⁴`,
six orders below the defect weight: the peeled power relation is
`head + h₀ · tail = C iotaK · h₀⁶`, so the order-`44` head vanishes at
the root of `h₀` on every live branch — a genuinely new relation the
row tower never reached.  Chamber-free, the head reduces modulo the
tenth-face root laws to the factored quotient
`p₃₁(a)² (27 b₆₂ - 30 a₄₁² - 5 p₂ + 9 λ p₃₁ - 40 p₃₁ w₁)(a) = 0`, and
with the `U`-load also to
`p₃₁(a)² (144 b₆₂ - 170 a₄₁² + 45 λ p₃₁ - 220 p₃₁ w₁)(a) = 0`.  On the
complementary factor the recorded `b₆₂` law collapses the cofactor to
`p₃₁(a)² (5 a₄₁² + 2 p₃₁ w₁)(a) = 0`.  On the `p₃₁(a) = 0` sibling the
chamber-free head is spent, but the deeper branch jet `p₃ = h₀² p₃₂`,
`q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`, `q₄ = h₀ q₄₁` refactors the numerator
through `h₀⁴⁵`, one order further: the order-`45` head vanishes at the
root and reduces, modulo the `s₁` law, the `q₄₁` law, and the `U`-load,
to the exact factored relation
`a₄₁(a) (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0` on `(a₄₁, p₂)` alone.

No branch is genuinely inconsistent, so none is closed: the sibling
survives carrying `a₄₁(a) = 0` or the irreducible quartic
`4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂² = 0` at the root, and the complementary
factor survives carrying `p₃₁(a)² (5 a₄₁² + 2 p₃₁ w₁)(a) = 0` — the
Keller boundary relation `E'(a) W(a) - D(a) X'(a) = j ≠ 0` lives on
`p₀, p₁, q₀, q₁`, which no head relation touches.  The ground constants
`ζ, η, iotaK` stay uncleared, the `χ₂`/`ψ₂` eliminations of the
fifteenth packet are preserved unchanged in the imported chain, and the
aligned face `N = 0` remains open.  The next mechanism is either the
aligned face (next unused aligned row: degree `12`), the degree-`4`
integral `κ` (which needs the `θ` tower restated on this chain), or
driving the new root relations into the retained branch laws at the
next `h`-order.

The degree-`5` depressed row lemma, the `z⁰` decic clearing, and the
`ι` machinery are restated here for the scale-two chain with
`terminal`/`_bridge` names to keep both chains importable; the imported
seventh-defect scratch supplies `η`, `depressedV610`, and the
degree-`7` row.  `d ι = 0` needs no constancy of the degree-`6`
integral `θ` — only the rows themselves.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000


/-! ## Weight-fifty cleared defect after a square root of the core -/

section BridgeIotaDepression610

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁰` coefficient. -/
def terminalDepressedX610 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- First residual of the degree-`5` row.  Equivalent to
`X - γ E - (5/6) δ D - (2/3) ε C - (1/2) ζ B - (1/3) η A
- (10/9) C E - (5/9) D² + (5/27) A² E + (10/27) A B D + (5/27) A C²
+ (5/27) B² C - (10/81) A² B² - (20/243) A³ C + (7/729) A⁵
- (4/9) α A E - (4/9) α B D - (2/9) α C² + (4/27) α A² C
+ (4/27) α A B² - (5/243) α A⁴ - (7/36) β A D - (7/36) β B C
+ (35/432) β A² B + (5/36) δ A B + (1/9) ε A²
- (3/4) L B E - (3/4) L C D + (3/8) L A B C + (3/16) L A² D
+ (1/16) L B³ - (3/32) L A³ B`
on the second- through eighth-face integrals. -/
def terminalIotaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0 : F) : F :=
  X0 - gammaResidual610 L A B C0 P R * E0 -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * D0 -
    (2 / 3 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * C0 -
    (1 / 2 : F) * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 * B -
    (1 / 3 : F) * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 * A -
    (10 / 9 : F) * C0 * E0 - (5 / 9 : F) * D0 ^ 2 +
    (5 / 27 : F) * A ^ 2 * E0 + (10 / 27 : F) * A * B * D0 +
    (5 / 27 : F) * A * C0 ^ 2 + (5 / 27 : F) * B ^ 2 * C0 -
    (10 / 81 : F) * A ^ 2 * B ^ 2 - (20 / 243 : F) * A ^ 3 * C0 +
    (7 / 729 : F) * A ^ 5 -
    (4 / 9 : F) * alphaResidual610 A P * A * E0 -
    (4 / 9 : F) * alphaResidual610 A P * B * D0 -
    (2 / 9 : F) * alphaResidual610 A P * C0 ^ 2 +
    (4 / 27 : F) * alphaResidual610 A P * A ^ 2 * C0 +
    (4 / 27 : F) * alphaResidual610 A P * A * B ^ 2 -
    (5 / 243 : F) * alphaResidual610 A P * A ^ 4 -
    (7 / 36 : F) * betaResidual610 L A B Q * A * D0 -
    (7 / 36 : F) * betaResidual610 L A B Q * B * C0 +
    (35 / 432 : F) * betaResidual610 L A B Q * A ^ 2 * B +
    (5 / 36 : F) * deltaResidual610 L A B C0 D0 P Q S0 * A * B +
    (1 / 9 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * A ^ 2 -
    (3 / 4 : F) * L * B * E0 - (3 / 4 : F) * L * C0 * D0 +
    (3 / 8 : F) * L * A * B * C0 + (3 / 16 : F) * L * A ^ 2 * D0 +
    (1 / 16 : F) * L * B ^ 3 - (3 / 32 : F) * L * A ^ 3 * B

set_option maxHeartbeats 8000000 in
/-- Polynomial numerator of `18 h⁵⁰ ι` on the ninth-power face. -/
def terminalClearedIotaDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F[X]) (lambda : F) : F[X] :=
    (30 : F[X]) * a0 * a2 * h ^ 48
    - (15 : F[X]) * a0 * a3 * a5 * h ^ 42
    - (9 : F[X]) * a0 * a3 * h ^ 47 * Polynomial.C lambda
    - (30 : F[X]) * a0 * a4 ^ 2 * h ^ 42
    + (18 : F[X]) * a0 * a4 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a0 * a4 * b8 * h ^ 38
    + (15 : F[X]) * a0 * a5 ^ 4 * h ^ 30
    - (9 : F[X]) * a0 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F[X]) * a0 * a5 * b7 * h ^ 38
    - (18 : F[X]) * a0 * b6 * h ^ 44
    + (15 : F[X]) * a1 ^ 2 * h ^ 48
    - (15 : F[X]) * a1 * a2 * a5 * h ^ 42
    - (9 : F[X]) * a1 * a2 * h ^ 47 * Polynomial.C lambda
    - (60 : F[X]) * a1 * a3 * a4 * h ^ 42
    + (18 : F[X]) * a1 * a3 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a3 * b8 * h ^ 38
    + (45 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (9 : F[X]) * a1 * a4 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a1 * a4 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a1 * a4 * b7 * h ^ 38
    - (15 : F[X]) * a1 * a5 ^ 5 * h ^ 24
    + (9 : F[X]) * a1 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F[X]) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F[X]) * a1 * a5 * b6 * h ^ 38
    - (15 : F[X]) * a1 * b5 * h ^ 44
    - (30 : F[X]) * a2 ^ 2 * a4 * h ^ 42
    + (9 : F[X]) * a2 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    + (12 : F[X]) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F[X]) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F[X]) * a2 * a3 * a4 * a5 * h ^ 36
    + (18 : F[X]) * a2 * a3 * a4 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a2 * a3 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a2 * a3 * b7 * h ^ 38
    + (30 : F[X]) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a2 * a4 ^ 2 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (36 : F[X]) * a2 * a4 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F[X]) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F[X]) * a2 * a4 * b6 * h ^ 38
    + (15 : F[X]) * a2 * a5 ^ 6 * h ^ 18
    - (9 : F[X]) * a2 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F[X]) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F[X]) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F[X]) * a2 * a5 * b5 * h ^ 38
    - (12 : F[X]) * a2 * b4 * h ^ 44
    + (15 : F[X]) * a3 ^ 3 * a5 * h ^ 36
    + (3 : F[X]) * a3 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (45 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a3 ^ 2 * a4 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (18 : F[X]) * a3 ^ 2 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (36 : F[X]) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F[X]) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F[X]) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 30
    - (9 : F[X]) * a3 * a4 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (30 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (54 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F[X]) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (45 : F[X]) * a3 * a4 * a5 ^ 4 * h ^ 23 * Polynomial.C lambda
    - (96 : F[X]) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F[X]) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F[X]) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F[X]) * a3 * a4 * b5 * h ^ 38
    - (15 : F[X]) * a3 * a5 ^ 7 * h ^ 12
    + (9 : F[X]) * a3 * a5 ^ 6 * h ^ 17 * Polynomial.C lambda
    + (24 : F[X]) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F[X]) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F[X]) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F[X]) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F[X]) * a3 * a5 * b4 * h ^ 38
    - (9 : F[X]) * a3 * b3 * h ^ 44
    - (6 : F[X]) * a4 ^ 5 * h ^ 30
    + (30 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (9 : F[X]) * a4 ^ 4 * a5 * h ^ 29 * Polynomial.C lambda
    + (6 : F[X]) * a4 ^ 4 * b8 * h ^ 26
    - (30 : F[X]) * a4 ^ 3 * a5 ^ 3 * h ^ 23 * Polynomial.C lambda
    - (48 : F[X]) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F[X]) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F[X]) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 5 * h ^ 17 * Polynomial.C lambda
    + (60 : F[X]) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F[X]) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F[X]) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F[X]) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F[X]) * a4 * a5 ^ 8 * h ^ 6
    - (9 : F[X]) * a4 * a5 ^ 7 * h ^ 11 * Polynomial.C lambda
    - (24 : F[X]) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F[X]) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F[X]) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F[X]) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F[X]) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F[X]) * a4 * a5 * b3 * h ^ 38
    - (6 : F[X]) * a4 * b2 * h ^ 44
    - (2 : F[X]) * a5 ^ 10
    + (1 : F[X]) * a5 ^ 9 * h ^ 5 * Polynomial.C lambda
    + (3 : F[X]) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F[X]) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F[X]) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F[X]) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F[X]) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F[X]) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F[X]) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F[X]) * a5 * b1 * h ^ 44
    + (18 : F[X]) * b0 * h ^ 50


/-- Exact denominator clearing for the decic `z⁰` coordinate on the
ninth-power face. -/
theorem terminalDepressedX610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    terminalDepressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 b1 b0 =
      (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
          36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
          1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
          46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
          1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
          60466176 * b0 * h ^ 50) /
        (60466176 * h ^ 50) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h60466176 : (60466176 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [terminalDepressedX610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      (a5 / (6 * h ^ 5)) ^ 10 -
          (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 9 +
        (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 8 -
          (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 7 +
        (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 6 -
          (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 5 +
        (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 4 -
          (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) ^ 3 +
        (b2 / h ^ 2) * (a5 / (6 * h ^ 5)) ^ 2 -
          (b1 / h) * (a5 / (6 * h ^ 5)) + b0 =
        (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
            36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
            1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
            46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
            1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
            60466176 * b0 * h ^ 50) /
          (60466176 * h ^ 50) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh50, h60466176]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh50, h60466176]
    ring
  exact hrewrite

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral
`X - γ E - (5/6) δ D - (2/3) ε C - (1/2) ζ B - (1/3) η A
- (10/9) C E - (5/9) D² + (5/27) A² E + (10/27) A B D + (5/27) A C²
+ (5/27) B² C - (10/81) A² B² - (20/243) A³ C + (7/729) A⁵
- (4/9) α A E - (4/9) α B D - (2/9) α C² + (4/27) α A² C
+ (4/27) α A B² - (5/243) α A⁴ - (7/36) β A D - (7/36) β B C
+ (35/432) β A² B + (5/36) δ A B + (1/9) ε A²
- (3/4) L B E - (3/4) L C D + (3/8) L A B C + (3/16) L A² D
+ (1/16) L B³ - (3/32) L A³ B`
against `h⁵⁰` on the ninth-power face. -/
theorem terminalIotaDefect_eq_cleared610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (18 : F) * h ^ 50 *
        terminalIotaResidual610
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
          (terminalDepressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1 b0) =
    (30 : F) * a0 * a2 * h ^ 48
    - (15 : F) * a0 * a3 * a5 * h ^ 42
    - (9 : F) * a0 * a3 * h ^ 47 * lambda
    - (30 : F) * a0 * a4 ^ 2 * h ^ 42
    + (18 : F) * a0 * a4 * a5 * h ^ 41 * lambda
    + (24 : F) * a0 * a4 * b8 * h ^ 38
    + (15 : F) * a0 * a5 ^ 4 * h ^ 30
    - (9 : F) * a0 * a5 ^ 3 * h ^ 35 * lambda
    - (24 : F) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F) * a0 * a5 * b7 * h ^ 38
    - (18 : F) * a0 * b6 * h ^ 44
    + (15 : F) * a1 ^ 2 * h ^ 48
    - (15 : F) * a1 * a2 * a5 * h ^ 42
    - (9 : F) * a1 * a2 * h ^ 47 * lambda
    - (60 : F) * a1 * a3 * a4 * h ^ 42
    + (18 : F) * a1 * a3 * a5 * h ^ 41 * lambda
    + (24 : F) * a1 * a3 * b8 * h ^ 38
    + (45 : F) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (9 : F) * a1 * a4 ^ 2 * h ^ 41 * lambda
    + (15 : F) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (27 : F) * a1 * a4 * a5 ^ 2 * h ^ 35 * lambda
    - (48 : F) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F) * a1 * a4 * b7 * h ^ 38
    - (15 : F) * a1 * a5 ^ 5 * h ^ 24
    + (9 : F) * a1 * a5 ^ 4 * h ^ 29 * lambda
    + (24 : F) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F) * a1 * a5 * b6 * h ^ 38
    - (15 : F) * a1 * b5 * h ^ 44
    - (30 : F) * a2 ^ 2 * a4 * h ^ 42
    + (9 : F) * a2 ^ 2 * a5 * h ^ 41 * lambda
    + (12 : F) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F) * a2 * a3 * a4 * a5 * h ^ 36
    + (18 : F) * a2 * a3 * a4 * h ^ 41 * lambda
    + (15 : F) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (27 : F) * a2 * a3 * a5 ^ 2 * h ^ 35 * lambda
    - (48 : F) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F) * a2 * a3 * b7 * h ^ 38
    + (30 : F) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (27 : F) * a2 * a4 ^ 2 * a5 * h ^ 35 * lambda
    - (24 : F) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (36 : F) * a2 * a4 * a5 ^ 3 * h ^ 29 * lambda
    + (72 : F) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F) * a2 * a4 * b6 * h ^ 38
    + (15 : F) * a2 * a5 ^ 6 * h ^ 18
    - (9 : F) * a2 * a5 ^ 5 * h ^ 23 * lambda
    - (24 : F) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F) * a2 * a5 * b5 * h ^ 38
    - (12 : F) * a2 * b4 * h ^ 44
    + (15 : F) * a3 ^ 3 * a5 * h ^ 36
    + (3 : F) * a3 ^ 3 * h ^ 41 * lambda
    + (45 : F) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (27 : F) * a3 ^ 2 * a4 * a5 * h ^ 35 * lambda
    - (24 : F) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (18 : F) * a3 ^ 2 * a5 ^ 3 * h ^ 29 * lambda
    + (36 : F) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F) * a3 * a4 ^ 3 * a5 * h ^ 30
    - (9 : F) * a3 * a4 ^ 3 * h ^ 35 * lambda
    + (30 : F) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (54 : F) * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 29 * lambda
    + (72 : F) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (45 : F) * a3 * a4 * a5 ^ 4 * h ^ 23 * lambda
    - (96 : F) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F) * a3 * a4 * b5 * h ^ 38
    - (15 : F) * a3 * a5 ^ 7 * h ^ 12
    + (9 : F) * a3 * a5 ^ 6 * h ^ 17 * lambda
    + (24 : F) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F) * a3 * a5 * b4 * h ^ 38
    - (9 : F) * a3 * b3 * h ^ 44
    - (6 : F) * a4 ^ 5 * h ^ 30
    + (30 : F) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (9 : F) * a4 ^ 4 * a5 * h ^ 29 * lambda
    + (6 : F) * a4 ^ 4 * b8 * h ^ 26
    - (30 : F) * a4 ^ 3 * a5 ^ 3 * h ^ 23 * lambda
    - (48 : F) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (27 : F) * a4 ^ 2 * a5 ^ 5 * h ^ 17 * lambda
    + (60 : F) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F) * a4 * a5 ^ 8 * h ^ 6
    - (9 : F) * a4 * a5 ^ 7 * h ^ 11 * lambda
    - (24 : F) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F) * a4 * a5 * b3 * h ^ 38
    - (6 : F) * a4 * b2 * h ^ 44
    - (2 : F) * a5 ^ 10
    + (1 : F) * a5 ^ 9 * h ^ 5 * lambda
    + (3 : F) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F) * a5 * b1 * h ^ 44
    + (18 : F) * b0 * h ^ 50 := by
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
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h60466176 : (60466176 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
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
  have hX :
      terminalDepressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 b0 =
        (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
            36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
            1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
            46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
            1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
            60466176 * b0 * h ^ 50) /
          (60466176 * h ^ 50) :=
    terminalDepressedX610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda
      hh hN
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
  simp only [terminalIotaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hX, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h32,
    h36, h54, h72, h81, h144, h216, h243, h324, h432, h648, h729, h7776,
    h11664, h46656, h93312, h186624, h60466176, hh10, hh15, hh20, hh25,
    hh30, hh35, hh40, hh45, hh50]
  ring

end BridgeIotaDepression610

/-! ## Degree-`5` depressed Jacobian coefficient -/

section BridgeIotaDepressedRow610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`5` Jacobian coefficient is
exactly `6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A' - D S' - 2 C T'
- 3 B U' - 4 A V' - 6 X'`. -/
theorem differentialJacobian_coeff_5_monicSexticDecic_bridge
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) +
        (3 : F) * g.coeff 3 * d (f.coeff 3) +
        (2 : F) * g.coeff 2 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 3) -
          (4 : F) * f.coeff 4 * d (g.coeff 2) -
          (6 : F) * d (g.coeff 0) := by
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
  have hmem08 : ((0, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 5 =
        (6 : F) * g.coeff 6 * d (f.coeff 0) +
          (5 : F) * g.coeff 5 * d (f.coeff 1) +
          (4 : F) * g.coeff 4 * d (f.coeff 2) +
          (3 : F) * g.coeff 3 * d (f.coeff 3) +
          (2 : F) * g.coeff 2 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne08_26 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne08_35 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne08_44 : ((0, 5) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne17_26 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne17_35 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne17_44 : ((1, 4) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne26_35 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne26_44 : ((2, 3) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne35_44 : ((3, 2) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hsubset :
        ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 1) := by
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
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 1 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
      ring
    have hder5g : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4g : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder5g, hder4g, hder3g, hder2g, hder1g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 5 =
        (1 : F) * f.coeff 1 * d (g.coeff 5) +
          (2 : F) * f.coeff 2 * d (g.coeff 4) +
          (3 : F) * f.coeff 3 * d (g.coeff 3) +
          (4 : F) * f.coeff 4 * d (g.coeff 2) +
          (6 : F) * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne08_26 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne08_35 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne08_53 : ((0, 5) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne17_26 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne17_35 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne17_53 : ((1, 4) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne26_35 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne26_53 : ((2, 3) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne35_53 : ((3, 2) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hsubset : ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 0) := by
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
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 0 := by
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


set_option maxHeartbeats 80000000 in
theorem terminalIotaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (hrow : (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A - (1 : F) * D0 * d S0 -
        (2 : F) * C0 * d T0 - (3 : F) * B * d U0 -
        (4 : F) * A * d V0 - (6 : F) * d X0 = 0) :
    d (terminalIotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0) = 0 := by
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
  have hXderiv : d X0 = R * d E0 + (5 / 6 : F) * S0 * d D0 +
      (2 / 3 : F) * T0 * d C0 + (1 / 2 : F) * U0 * d B +
      (1 / 3 : F) * V0 * d A - (1 / 6 : F) * D0 * d S0 -
      (1 / 3 : F) * C0 * d T0 - (1 / 2 : F) * B * d U0 -
      (2 / 3 : F) * A * d V0 := by
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
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3]
  have h19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_inv, h9]
  have h432 : d (432 : F) = 0 := d.map_natCast 432
  have h729 : d (729 : F) = 0 := d.map_natCast 729
  have h35432 : d (35 / 432 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h432, h35]
  have h7729 : d (7 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729, h7]
  have h536 : d (5 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h5]
  have h1081 : d (10 / 81 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h81, h10]
  have h5243 : d (5 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h5]
  have h481 : d (4 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h4]
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h3]
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h25 : d (25 : F) = 0 := d.map_natCast 25
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
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  simp only [terminalIotaResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, h19, h23, h53,
    h32, h43, h76, h56c, h109, h49, h772, h581, h736, h1027, h572, h527,
    h427, h351296, h20243, h38, h34, h316, h3128, h116, h29, h59, h89,
    h2027, h35432, h7729, h536, h1081, h5243, h481, h332, h52, h78, h94,
    h98, h258, h1516, hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta,
    heta, hsq, hsqB, hsqC, hsqD, hcub, hcubB, hquar, hquint, pow_two,
    pow_three, zero_mul, add_zero, mul_zero]
  rw [hXderiv, hVderiv, hUderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, pow_two, pow_three]
  ring

end BridgeIotaDepressedRow610

section BridgeAffineDecic610

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁰` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff0_610_bridge
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 0 =
      r ^ 10 - (p.coeff 9 / h ^ 9) * r ^ 9 +
        (p.coeff 8 / h ^ 8) * r ^ 8 -
        (p.coeff 7 / h ^ 7) * r ^ 7 +
        (p.coeff 6 / h ^ 6) * r ^ 6 -
        (p.coeff 5 / h ^ 5) * r ^ 5 +
        (p.coeff 4 / h ^ 4) * r ^ 4 -
        (p.coeff 3 / h ^ 3) * r ^ 3 +
        (p.coeff 2 / h ^ 2) * r ^ 2 -
        (p.coeff 1 / h) * r + p.coeff 0 := by
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
  have hlow0 :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        p.coeff 0 := by
    have hC : plow = Polynomial.C (plow.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hplowDeg
    have hcoeff0 : plow.coeff 0 = p.coeff 0 := by
      simp [plow]
    rw [hC, Polynomial.C_comp, Polynomial.coeff_C, if_pos rfl, hcoeff0]
  have h10_0 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        r ^ 10 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 0 hh]
    have hle : (0 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hp10, hbin, pow_zero]
    field_simp [hh]; ring
  have h9_0 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 9 / h ^ 9) * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 0 hh]
    have hle : (0 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h8_0 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 8 / h ^ 8) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 0 hh]
    have hle : (0 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h7_0 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 7 / h ^ 7) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 0 hh]
    have hle : (0 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h6_0 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 6 / h ^ 6) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 0 hh]
    have hle : (0 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h5_0 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 5 / h ^ 5) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 0 hh]
    have hle : (0 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h4_0 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 4 / h ^ 4) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 0 hh]
    have hle : (0 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h3_0 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 3 / h ^ 3) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 0 hh]
    have hle : (0 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_three]
    field_simp [hh]; ring
  have h2_0 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 2 / h ^ 2) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 0 hh]
    have hle : (0 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_two]
    field_simp [hh]; ring
  have h1_0 :
      ((Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 1 / h) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 0 hh]
    have hle : (0 : ℕ) ≤ 1 := by omega
    have hbin : (1 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_one]
    field_simp [hh]; ring
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, h10_0, h9_0, h8_0, h7_0, h6_0, h5_0, h4_0, h3_0,
    h2_0, h1_0, hlow0]
  ring

end BridgeAffineDecic610

section NonzeroTerminalIotaClearing610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The ninth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁵⁰`. -/
theorem nonzeroFace610_terminalIotaPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ kappa : k,
      terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C kappa * h0 ^ 50 := by
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
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
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
  have hg0 :
      g.coeff 0 =
        terminalDepressedX610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 b0 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff0_610_bridge (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [terminalDepressedX610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
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
  have hkappa0deriv :
      ratFuncDerivation68
        (terminalIotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 0)) = 0 :=
    terminalIotaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 0) hLconst halpha0 hbeta0
      hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      (by simpa using hrow5)
  obtain ⟨kappa0, hkappa0⟩ :
      ∃ a : k,
        terminalIotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 0) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hkappa0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        (18 : RatFunc k) * hRF ^ 50 *
          terminalIotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 0) := by
    have hF := terminalIotaDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 b0 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [terminalClearedIotaDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, b1, b0, terminalIotaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, zetaResidual610, etaResidual610, hf4, hf3, hf2,
      hf1, hf0, hg0, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (18 * kappa0) * h0 ^ 50) := by
    rw [hclear, hkappa0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨18 * kappa0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget
end NonzeroTerminalIotaClearing610

/-! ## Jet head and tail of the cleared `ι` defect -/

section BridgeIotaJet610

variable {R : Type*} [CommRing R]

/-- Order-`44` head of the jet-substituted cleared `ι` defect: the
coefficient of `h⁴⁴` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `terminalClearedIotaDefect610`. -/
def bridgeIotaJetHead610 (w1 a41 p31 s1 u1 b62 q52 p2 q4 lam : R) : R :=
    - (12 : R) * p2 * q4
    + (21 : R) * p31 * u1 * p2
    - (30 : R) * p31 ^ 2 * p2
    + (9 : R) * p31 ^ 2 * b62
    + (3 : R) * p31 ^ 3 * lam
    + (15 : R) * a41 * p31 * q52
    - (24 : R) * a41 * p31 ^ 2 * s1
    + (6 : R) * a41 ^ 2 * q4
    - (21 : R) * a41 ^ 2 * p31 * u1
    + (45 : R) * a41 ^ 2 * p31 ^ 2
    + (12 : R) * w1 * p31 * q4
    - (21 : R) * w1 * p31 ^ 2 * u1
    + (15 : R) * w1 * p31 ^ 3

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `ι` defect above order `h⁴⁵`. -/
def bridgeIotaJetTail610
    (hh w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 q0 lam : R) : R :=
    (12 : R) * s1 * p2 ^ 2
    - (9 : R) * p31 * q3
    - (30 : R) * a41 * p2 ^ 2
    + (18 : R) * a41 * b62 * p2
    - (24 : R) * a41 ^ 2 * s1 * p2
    + (30 : R) * a41 ^ 3 * p2
    - (6 : R) * a41 ^ 3 * b62
    + (6 : R) * a41 ^ 4 * s1
    - (6 : R) * a41 ^ 5
    + (15 : R) * w1 * q52 * p2
    - (48 : R) * w1 * p31 * s1 * p2
    - (42 : R) * w1 * a41 * u1 * p2
    + (90 : R) * w1 * a41 * p31 * p2
    - (36 : R) * w1 * a41 * p31 * b62
    - (15 : R) * w1 * a41 ^ 2 * q52
    + (72 : R) * w1 * a41 ^ 2 * p31 * s1
    + (21 : R) * w1 * a41 ^ 3 * u1
    - (75 : R) * w1 * a41 ^ 3 * p31
    - (15 : R) * w1 ^ 2 * p31 * q52
    + (36 : R) * w1 ^ 2 * p31 ^ 2 * s1
    - (12 : R) * w1 ^ 2 * a41 * q4
    + (63 : R) * w1 ^ 2 * a41 * p31 * u1
    - (45 : R) * w1 ^ 2 * a41 * p31 ^ 2
    + (18 : R) * lam * a41 * p31 * p2
    - (9 : R) * lam * a41 ^ 3 * p31
    - (27 : R) * lam * w1 * a41 * p31 ^ 2
    - (15 : R) * hh * q52 * p1
    + (24 : R) * hh * p31 * s1 * p1
    + (21 : R) * hh * a41 * u1 * p1
    - (60 : R) * hh * a41 * p31 * p1
    + (9 : R) * hh * w1 * a41 * q3
    - (18 : R) * hh * w1 ^ 2 * b62 * p2
    + (72 : R) * hh * w1 ^ 2 * a41 * s1 * p2
    - (45 : R) * hh * w1 ^ 2 * a41 ^ 2 * p2
    + (27 : R) * hh * w1 ^ 2 * a41 ^ 2 * b62
    - (48 : R) * hh * w1 ^ 2 * a41 ^ 3 * s1
    + (30 : R) * hh * w1 ^ 2 * a41 ^ 4
    + (21 : R) * hh * w1 ^ 3 * u1 * p2
    + (15 : R) * hh * w1 ^ 3 * p31 * p2
    + (18 : R) * hh * w1 ^ 3 * p31 * b62
    + (15 : R) * hh * w1 ^ 3 * a41 * q52
    - (96 : R) * hh * w1 ^ 3 * a41 * p31 * s1
    - (42 : R) * hh * w1 ^ 3 * a41 ^ 2 * u1
    + (30 : R) * hh * w1 ^ 3 * a41 ^ 2 * p31
    + (3 : R) * hh * w1 ^ 4 * q4
    - (21 : R) * hh * w1 ^ 4 * p31 * u1
    - (15 : R) * hh * w1 ^ 4 * p31 ^ 2
    + (9 : R) * hh * lam * w1 * p2 ^ 2
    - (27 : R) * hh * lam * w1 * a41 ^ 2 * p2
    + (9 : R) * hh * lam * w1 * a41 ^ 4
    - (27 : R) * hh * lam * w1 ^ 2 * p31 * p2
    + (54 : R) * hh * lam * w1 ^ 2 * a41 ^ 2 * p31
    + (18 : R) * hh * lam * w1 ^ 3 * p31 ^ 2
    - (6 : R) * hh ^ 2 * a41 * q2
    - (15 : R) * hh ^ 2 * w1 * p2 * p1
    + (18 : R) * hh ^ 2 * w1 * b62 * p1
    - (48 : R) * hh ^ 2 * w1 * a41 * s1 * p1
    + (45 : R) * hh ^ 2 * w1 * a41 ^ 2 * p1
    - (21 : R) * hh ^ 2 * w1 ^ 2 * u1 * p1
    - (3 : R) * hh ^ 2 * w1 ^ 3 * q3
    - (24 : R) * hh ^ 2 * w1 ^ 4 * s1 * p2
    - (30 : R) * hh ^ 2 * w1 ^ 4 * a41 * p2
    - (18 : R) * hh ^ 2 * w1 ^ 4 * a41 * b62
    + (60 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * s1
    - (3 : R) * hh ^ 2 * w1 ^ 5 * q52
    + (24 : R) * hh ^ 2 * w1 ^ 5 * p31 * s1
    + (21 : R) * hh ^ 2 * w1 ^ 5 * a41 * u1
    + (45 : R) * hh ^ 2 * w1 ^ 5 * a41 * p31
    - (9 : R) * hh ^ 2 * lam * p2 * p1
    + (9 : R) * hh ^ 2 * lam * a41 ^ 2 * p1
    + (18 : R) * hh ^ 2 * lam * w1 * p31 * p1
    + (36 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 * p2
    - (30 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 ^ 3
    - (45 : R) * hh ^ 2 * lam * w1 ^ 4 * a41 * p31
    + (15 : R) * hh ^ 3 * p1 ^ 2
    + (30 : R) * hh ^ 3 * p2 * p0
    - (18 : R) * hh ^ 3 * b62 * p0
    + (24 : R) * hh ^ 3 * a41 * s1 * p0
    - (30 : R) * hh ^ 3 * a41 ^ 2 * p0
    + (21 : R) * hh ^ 3 * w1 * u1 * p0
    - (15 : R) * hh ^ 3 * w1 * p31 * p0
    + (3 : R) * hh ^ 3 * w1 ^ 2 * q2
    + (24 : R) * hh ^ 3 * w1 ^ 3 * s1 * p1
    + (15 : R) * hh ^ 3 * w1 ^ 3 * a41 * p1
    + (15 : R) * hh ^ 3 * w1 ^ 6 * p2
    + (3 : R) * hh ^ 3 * w1 ^ 6 * b62
    - (24 : R) * hh ^ 3 * w1 ^ 6 * a41 * s1
    - (30 : R) * hh ^ 3 * w1 ^ 6 * a41 ^ 2
    - (3 : R) * hh ^ 3 * w1 ^ 7 * u1
    - (15 : R) * hh ^ 3 * w1 ^ 7 * p31
    - (9 : R) * hh ^ 3 * lam * p31 * p0
    - (27 : R) * hh ^ 3 * lam * w1 ^ 2 * a41 * p1
    - (9 : R) * hh ^ 3 * lam * w1 ^ 5 * p2
    + (27 : R) * hh ^ 3 * lam * w1 ^ 5 * a41 ^ 2
    + (9 : R) * hh ^ 3 * lam * w1 ^ 6 * p31
    - (3 : R) * hh ^ 4 * w1 * q1
    - (24 : R) * hh ^ 4 * w1 ^ 2 * s1 * p0
    - (15 : R) * hh ^ 4 * w1 ^ 5 * p1
    + (3 : R) * hh ^ 4 * w1 ^ 8 * s1
    + (15 : R) * hh ^ 4 * w1 ^ 8 * a41
    + (18 : R) * hh ^ 4 * lam * w1 * a41 * p0
    + (9 : R) * hh ^ 4 * lam * w1 ^ 4 * p1
    - (9 : R) * hh ^ 4 * lam * w1 ^ 7 * a41
    + (18 : R) * hh ^ 5 * q0
    + (15 : R) * hh ^ 5 * w1 ^ 4 * p0
    - (2 : R) * hh ^ 5 * w1 ^ 10
    - (9 : R) * hh ^ 5 * lam * w1 ^ 3 * p0
    + (1 : R) * hh ^ 5 * lam * w1 ^ 9

/-- Order-`45` head of the cleared `ι` defect on the deeper
`p₃₁(a) = 0` sibling jet `p₃ = h² p₃₂`, `q₇ = h⁶ u₂`, `q₅ = h³ q₅₃`,
`q₄ = h q₄₁`. -/
def bridgeIotaLeftHead610 (a41 s1 b62 p2 q41 : R) : R :=
    - (12 : R) * p2 * q41
    + (12 : R) * s1 * p2 ^ 2
    - (30 : R) * a41 * p2 ^ 2
    + (18 : R) * a41 * b62 * p2
    + (6 : R) * a41 ^ 2 * q41
    - (24 : R) * a41 ^ 2 * s1 * p2
    + (30 : R) * a41 ^ 3 * p2
    - (6 : R) * a41 ^ 3 * b62
    + (6 : R) * a41 ^ 4 * s1
    - (6 : R) * a41 ^ 5

set_option maxHeartbeats 40000000 in
/-- Tail of the deeper sibling jet above order `h⁴⁶`. -/
def bridgeIotaLeftTail610
    (hh w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 q0 lam : R) : R :=
    - (9 : R) * p32 * q3
    + (21 : R) * p32 * u2 * p2
    - (30 : R) * p32 ^ 2 * p2
    + (9 : R) * p32 ^ 2 * b62
    + (15 : R) * a41 * p32 * q53
    - (24 : R) * a41 * p32 ^ 2 * s1
    - (21 : R) * a41 ^ 2 * p32 * u2
    + (45 : R) * a41 ^ 2 * p32 ^ 2
    + (15 : R) * w1 * q53 * p2
    + (12 : R) * w1 * p32 * q41
    - (48 : R) * w1 * p32 * s1 * p2
    + (9 : R) * w1 * a41 * q3
    - (42 : R) * w1 * a41 * u2 * p2
    + (90 : R) * w1 * a41 * p32 * p2
    - (36 : R) * w1 * a41 * p32 * b62
    - (15 : R) * w1 * a41 ^ 2 * q53
    + (72 : R) * w1 * a41 ^ 2 * p32 * s1
    + (21 : R) * w1 * a41 ^ 3 * u2
    - (75 : R) * w1 * a41 ^ 3 * p32
    - (18 : R) * w1 ^ 2 * b62 * p2
    - (12 : R) * w1 ^ 2 * a41 * q41
    + (72 : R) * w1 ^ 2 * a41 * s1 * p2
    - (45 : R) * w1 ^ 2 * a41 ^ 2 * p2
    + (27 : R) * w1 ^ 2 * a41 ^ 2 * b62
    - (48 : R) * w1 ^ 2 * a41 ^ 3 * s1
    + (30 : R) * w1 ^ 2 * a41 ^ 4
    + (18 : R) * lam * a41 * p32 * p2
    - (9 : R) * lam * a41 ^ 3 * p32
    + (9 : R) * lam * w1 * p2 ^ 2
    - (27 : R) * lam * w1 * a41 ^ 2 * p2
    + (9 : R) * lam * w1 * a41 ^ 4
    - (15 : R) * hh * q53 * p1
    + (24 : R) * hh * p32 * s1 * p1
    - (6 : R) * hh * a41 * q2
    + (21 : R) * hh * a41 * u2 * p1
    - (60 : R) * hh * a41 * p32 * p1
    - (15 : R) * hh * w1 * p2 * p1
    + (18 : R) * hh * w1 * b62 * p1
    - (21 : R) * hh * w1 * p32 ^ 2 * u2
    + (15 : R) * hh * w1 * p32 ^ 3
    - (48 : R) * hh * w1 * a41 * s1 * p1
    + (45 : R) * hh * w1 * a41 ^ 2 * p1
    - (15 : R) * hh * w1 ^ 2 * p32 * q53
    + (36 : R) * hh * w1 ^ 2 * p32 ^ 2 * s1
    + (63 : R) * hh * w1 ^ 2 * a41 * p32 * u2
    - (45 : R) * hh * w1 ^ 2 * a41 * p32 ^ 2
    - (3 : R) * hh * w1 ^ 3 * q3
    + (21 : R) * hh * w1 ^ 3 * u2 * p2
    + (15 : R) * hh * w1 ^ 3 * p32 * p2
    + (18 : R) * hh * w1 ^ 3 * p32 * b62
    + (15 : R) * hh * w1 ^ 3 * a41 * q53
    - (96 : R) * hh * w1 ^ 3 * a41 * p32 * s1
    - (42 : R) * hh * w1 ^ 3 * a41 ^ 2 * u2
    + (30 : R) * hh * w1 ^ 3 * a41 ^ 2 * p32
    + (3 : R) * hh * w1 ^ 4 * q41
    - (24 : R) * hh * w1 ^ 4 * s1 * p2
    - (30 : R) * hh * w1 ^ 4 * a41 * p2
    - (18 : R) * hh * w1 ^ 4 * a41 * b62
    + (60 : R) * hh * w1 ^ 4 * a41 ^ 2 * s1
    - (9 : R) * hh * lam * p2 * p1
    + (3 : R) * hh * lam * p32 ^ 3
    + (9 : R) * hh * lam * a41 ^ 2 * p1
    - (27 : R) * hh * lam * w1 * a41 * p32 ^ 2
    - (27 : R) * hh * lam * w1 ^ 2 * p32 * p2
    + (54 : R) * hh * lam * w1 ^ 2 * a41 ^ 2 * p32
    + (36 : R) * hh * lam * w1 ^ 3 * a41 * p2
    - (30 : R) * hh * lam * w1 ^ 3 * a41 ^ 3
    + (15 : R) * hh ^ 2 * p1 ^ 2
    + (30 : R) * hh ^ 2 * p2 * p0
    - (18 : R) * hh ^ 2 * b62 * p0
    + (24 : R) * hh ^ 2 * a41 * s1 * p0
    - (30 : R) * hh ^ 2 * a41 ^ 2 * p0
    + (3 : R) * hh ^ 2 * w1 ^ 2 * q2
    - (21 : R) * hh ^ 2 * w1 ^ 2 * u2 * p1
    + (24 : R) * hh ^ 2 * w1 ^ 3 * s1 * p1
    + (15 : R) * hh ^ 2 * w1 ^ 3 * a41 * p1
    - (21 : R) * hh ^ 2 * w1 ^ 4 * p32 * u2
    - (15 : R) * hh ^ 2 * w1 ^ 4 * p32 ^ 2
    - (3 : R) * hh ^ 2 * w1 ^ 5 * q53
    + (24 : R) * hh ^ 2 * w1 ^ 5 * p32 * s1
    + (21 : R) * hh ^ 2 * w1 ^ 5 * a41 * u2
    + (45 : R) * hh ^ 2 * w1 ^ 5 * a41 * p32
    + (15 : R) * hh ^ 2 * w1 ^ 6 * p2
    + (3 : R) * hh ^ 2 * w1 ^ 6 * b62
    - (24 : R) * hh ^ 2 * w1 ^ 6 * a41 * s1
    - (30 : R) * hh ^ 2 * w1 ^ 6 * a41 ^ 2
    + (18 : R) * hh ^ 2 * lam * w1 * p32 * p1
    - (27 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 * p1
    + (18 : R) * hh ^ 2 * lam * w1 ^ 3 * p32 ^ 2
    - (45 : R) * hh ^ 2 * lam * w1 ^ 4 * a41 * p32
    - (9 : R) * hh ^ 2 * lam * w1 ^ 5 * p2
    + (27 : R) * hh ^ 2 * lam * w1 ^ 5 * a41 ^ 2
    - (3 : R) * hh ^ 3 * w1 * q1
    + (21 : R) * hh ^ 3 * w1 * u2 * p0
    - (15 : R) * hh ^ 3 * w1 * p32 * p0
    - (24 : R) * hh ^ 3 * w1 ^ 2 * s1 * p0
    - (15 : R) * hh ^ 3 * w1 ^ 5 * p1
    - (3 : R) * hh ^ 3 * w1 ^ 7 * u2
    - (15 : R) * hh ^ 3 * w1 ^ 7 * p32
    + (3 : R) * hh ^ 3 * w1 ^ 8 * s1
    + (15 : R) * hh ^ 3 * w1 ^ 8 * a41
    - (9 : R) * hh ^ 3 * lam * p32 * p0
    + (18 : R) * hh ^ 3 * lam * w1 * a41 * p0
    + (9 : R) * hh ^ 3 * lam * w1 ^ 4 * p1
    + (9 : R) * hh ^ 3 * lam * w1 ^ 6 * p32
    - (9 : R) * hh ^ 3 * lam * w1 ^ 7 * a41
    + (18 : R) * hh ^ 4 * q0
    + (15 : R) * hh ^ 4 * w1 ^ 4 * p0
    - (2 : R) * hh ^ 4 * w1 ^ 10
    - (9 : R) * hh ^ 4 * lam * w1 ^ 3 * p0
    + (1 : R) * hh ^ 4 * lam * w1 ^ 9

end BridgeIotaJet610

/-! ## Jet factorizations of the cleared defect -/

section BridgeIotaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the fifteenth-face jet the cleared `ι` defect factors exactly as
`h⁴⁴` times its order-`44` head plus `h` times the tail. -/
theorem terminalClearedIotaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 q0 : k[X])
    (lambda : k) :
    terminalClearedIotaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41) (h * p31)
        p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62) (h ^ 2 * q52)
        q4 q3 q2 q1 q0 lambda =
      h ^ 44 *
        (bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 p2 q4
            (Polynomial.C lambda) +
          h * bridgeIotaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0
            q4 q3 q2 q1 q0 (Polynomial.C lambda)) := by
  simp only [terminalClearedIotaDefect610, bridgeIotaJetHead610,
    bridgeIotaJetTail610]
  ring

set_option maxHeartbeats 40000000 in
/-- On the deeper `p₃₁(a) = 0` sibling jet the cleared `ι` defect
factors exactly as `h⁴⁵` times its order-`45` head plus `h` times the
sibling tail. -/
theorem terminalClearedIotaDefect610_leftJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 q0 : k[X])
    (lambda : k) :
    terminalClearedIotaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1) (h ^ 6 * u2) (h ^ 4 * b62)
        (h ^ 3 * q53) (h * q41) q3 q2 q1 q0 lambda =
      h ^ 45 *
        (bridgeIotaLeftHead610 a41 s1 b62 p2 q41 +
          h * bridgeIotaLeftTail610 h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0
            q41 q3 q2 q1 q0 (Polynomial.C lambda)) := by
  simp only [terminalClearedIotaDefect610, bridgeIotaLeftHead610,
    bridgeIotaLeftTail610]
  ring

/-- Evaluation commutes with the order-`44` head. -/
theorem bridgeIotaJetHead610_eval
    (w1 a41 p31 s1 u1 b62 q52 p2 q4 : k[X]) (lam x : k) :
    (bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 p2 q4
        (Polynomial.C lam)).eval x =
      bridgeIotaJetHead610 (w1.eval x) (a41.eval x) (p31.eval x)
        (s1.eval x) (u1.eval x) (b62.eval x) (q52.eval x) (p2.eval x)
        (q4.eval x) lam := by
  simp only [bridgeIotaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one,
    Polynomial.eval_C]

/-- Evaluation commutes with the order-`45` sibling head. -/
theorem bridgeIotaLeftHead610_eval
    (a41 s1 b62 p2 q41 : k[X]) (x : k) :
    (bridgeIotaLeftHead610 a41 s1 b62 p2 q41).eval x =
      bridgeIotaLeftHead610 (a41.eval x) (s1.eval x) (b62.eval x)
        (p2.eval x) (q41.eval x) := by
  simp only [bridgeIotaLeftHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]

end BridgeIotaJetFactor610

/-! ## Scalar consequences of the vanishing order-`44` head -/

section BridgeIotaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`44` head modulo the
tenth-face root laws: the head carries the factored quotient
`p₃₁² (27 b₆₂ - 30 a₄₁² - 5 p₂ + 9 λ p₃₁ - 40 p₃₁ w₁)`. -/
theorem bridgeIota_chamberFree_residual610
    (w1 a41 p31 s1 u1 b62 q52 p2 q4 lam : F)
    (hhead : bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 p2 q4 lam =
      0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    p31 ^ 2 * ((27 : F) * b62 - (30 : F) * a41 ^ 2 - (5 : F) * p2 +
      (9 : F) * lam * p31 - (40 : F) * p31 * w1) = 0 := by
  simp only [bridgeIotaJetHead610] at hhead
  linear_combination (3 : F) * hhead + (24 : F) * a41 * p31 ^ 2 * hs +
      ((21 : F) * a41 ^ 2 * p31 - (21 : F) * p2 * p31 +
        (21 : F) * p31 ^ 2 * w1) * hu -
      (5 : F) * a41 * p31 * hq52 +
      (-(2 : F) * a41 ^ 2 + (4 : F) * p2 - (4 : F) * p31 * w1) * hq4

set_option maxHeartbeats 4000000 in
/-- With the chamber-free `U`-load the factored quotient sharpens to
`p₃₁² (144 b₆₂ - 170 a₄₁² + 45 λ p₃₁ - 220 p₃₁ w₁)`. -/
theorem bridgeIota_uload_residual610
    (w1 a41 p31 s1 u1 b62 q52 p2 q4 lam : F)
    (hhead : bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 p2 q4 lam =
      0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lam * p31 +
      (30 : F) * p2 + (20 : F) * p31 * w1 = 0) :
    p31 ^ 2 * ((144 : F) * b62 - (170 : F) * a41 ^ 2 +
      (45 : F) * lam * p31 - (220 : F) * p31 * w1) = 0 := by
  simp only [bridgeIotaJetHead610] at hhead
  linear_combination (18 : F) * hhead + p31 ^ 2 * hU +
      (144 : F) * a41 * p31 ^ 2 * hs +
      ((126 : F) * a41 ^ 2 * p31 - (126 : F) * p2 * p31 +
        (126 : F) * p31 ^ 2 * w1) * hu -
      (30 : F) * a41 * p31 * hq52 +
      (-(12 : F) * a41 ^ 2 + (24 : F) * p2 - (24 : F) * p31 * w1) * hq4

set_option maxHeartbeats 4000000 in
/-- On the complementary factor the recorded `b₆₂` law collapses the
factored quotient to `p₃₁² (5 a₄₁² + 2 p₃₁ w₁)`. -/
theorem bridgeIota_comp_residual610
    (w1 a41 p31 s1 u1 b62 q52 p2 q4 lam : F)
    (hhead : bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 p2 q4 lam =
      0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lam * p31 +
      (30 : F) * p2 + (20 : F) * p31 * w1 = 0)
    (hcomp : (144 : F) * b62 - (120 : F) * a41 ^ 2 +
      (45 : F) * lam * p31 - (200 : F) * p31 * w1 = 0) :
    p31 ^ 2 * ((5 : F) * a41 ^ 2 + (2 : F) * p31 * w1) = 0 := by
  simp only [bridgeIotaJetHead610] at hhead
  linear_combination (-(9 / 5 : F)) * hhead -
      (1 / 10 : F) * p31 ^ 2 * hU -
      (72 / 5 : F) * a41 * p31 ^ 2 * hs +
      (-(63 / 5 : F) * a41 ^ 2 * p31 + (63 / 5 : F) * p2 * p31 -
        (63 / 5 : F) * p31 ^ 2 * w1) * hu +
      (3 : F) * a41 * p31 * hq52 +
      ((6 / 5 : F) * a41 ^ 2 - (12 / 5 : F) * p2 +
        (12 / 5 : F) * p31 * w1) * hq4 +
      (1 / 10 : F) * p31 ^ 2 * hcomp

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁(a) = 0` sibling the vanishing order-`45` head reduces,
modulo the `s₁` law, the `q₄₁` law, and the `U`-load, to the exact
factored relation `a₄₁ (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²) = 0` on
`(a₄₁, p₂)` alone. -/
theorem bridgeIota_left_residual610
    (w1 a41 p31 s1 b62 p2 q41 lam : F)
    (hhead : bridgeIotaLeftHead610 a41 s1 b62 p2 q41 = 0)
    (hz : p31 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hq41 : (81 : F) * q41 - (90 : F) * a41 * p2 +
      (5 : F) * a41 ^ 3 = 0)
    (hU : (10 : F) * a41 ^ 2 - (18 : F) * b62 - (9 : F) * lam * p31 +
      (30 : F) * p2 + (20 : F) * p31 * w1 = 0) :
    a41 * ((4 : F) * a41 ^ 4 - (35 : F) * p2 * a41 ^ 2 +
      (90 : F) * p2 ^ 2) = 0 := by
  simp only [bridgeIotaLeftHead610] at hhead
  linear_combination (27 / 2 : F) * hhead +
      (-(27 : F) * a41 ^ 4 + (108 : F) * a41 ^ 2 * p2 -
        (54 : F) * p2 ^ 2) * hs +
      (-a41 ^ 2 + (2 : F) * p2) * hq41 +
      (-(9 / 2 : F) * a41 ^ 3 + (27 / 2 : F) * a41 * p2) * hU +
      (-(81 / 2 : F) * a41 ^ 3 * lam + (90 : F) * a41 ^ 3 * w1 +
        (243 / 2 : F) * a41 * lam * p2 -
        (270 : F) * a41 * p2 * w1) * hz

end BridgeIotaScalars610

/-! ## Finite local terminal integral bridge packet -/

section NonzeroTerminalIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local terminal integral bridge: the fifteenth final-row
packet together with the literal-source `h`-adic clearing of the
degree-`5` first integral `ι` — the lowest of the uncleared degree-`5`
through degree-`1` integrals that admits an exact isolated
construction — and its jet-peeled consequences.  The cleared defect is
`C iotaK * h₀⁵⁰` for a ground constant `iotaK` (not claimed zero), the
fifteenth-face jet factors it through `h₀⁴⁴`, so the order-`44` head
vanishes at the root on every branch and carries the chamber-free
factored quotients.  On the `p₃₁(a) = 0` sibling the deeper jet
refactors through `h₀⁴⁵` and yields
`a₄₁(a) (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0`; on the complementary
factor the quotient collapses to
`p₃₁(a)² (5 a₄₁² + 2 p₃₁ w₁)(a) = 0`.  Neither branch is closed. -/
theorem nonzeroFace610_linearRoot_terminalIntegralBridge
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
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]) (iotaK : k),
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
                a41.eval a * ((4 : k) * (a41.eval a) ^ 4 -
                    (35 : k) * (p.coeff 2).eval a *
                      (a41.eval a) ^ 2 +
                    (90 : k) * ((p.coeff 2).eval a) ^ 2) = 0) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            (p31.eval a) ^ 2 * ((5 : k) * (a41.eval a) ^ 2 +
              (2 : k) * p31.eval a * w1.eval a) = 0)) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, halt⟩ :=
    nonzeroFace610_linearRoot_fifteenthFinalRow p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨iotaK, hpow⟩ :=
    nonzeroFace610_terminalIotaPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hpowJet :
      terminalClearedIotaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
          lambda =
        Polynomial.C iotaK * h0 ^ 50 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hpow
  have hpeel :
      bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
            (q.coeff 4) (Polynomial.C lambda) +
          h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
            (Polynomial.C lambda) =
        Polynomial.C iotaK * h0 ^ 6 := by
    have h44 : (h0 : k[X]) ^ 44 ≠ 0 := pow_ne_zero 44 hh0
    apply mul_left_cancel₀ h44
    rw [← terminalClearedIotaDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda]
    rw [hpowJet]
    ring
  have hheadeval :
      bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
          (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
          ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 := by
    have hev := congrArg (Polynomial.eval a) hpeel
    have h6z : (0 : k) ^ 6 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeIotaJetHead610_eval, h6z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hres1 :=
    bridgeIota_chamberFree_residual610 (w1.eval a) (a41.eval a)
      (p31.eval a) (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
      ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda hheadeval hMs
      hTu hVq hWq
  have hres2 :=
    bridgeIota_uload_residual610 (w1.eval a) (a41.eval a)
      (p31.eval a) (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
      ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda hheadeval hMs
      hTu hVq hWq hUload
  refine ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs,
    hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hpow,
    hpeel, hheadeval, hres1, hres2, ?_⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, _hchieq, _hchival,
      _hchi2eq, _hchi2val, _heli⟩⟩ |
      ⟨htp, hb62form, omega, psi, psi2, _homega, _homegaval, _hpsieq,
        _hpsival, _hpsi2eq, _hpsi2val, _heli2⟩
  · have hpowJetL :
        terminalClearedIotaDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
            (h0 ^ 2 * p32) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (h0 ^ 7 * s1) (h0 ^ 6 * u2) (h0 ^ 4 * b62) (h0 ^ 3 * q53)
            (h0 * q41) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 := by
      rw [← hw, ← ha4s, ← hp3u, ← hs, ← hq7u, ← hb6s, ← hq5u, ← hq4u]
      exact hpow
    have hpeelL :
        bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 5 := by
      have h45 : (h0 : k[X]) ^ 45 ≠ 0 := pow_ne_zero 45 hh0
      apply mul_left_cancel₀ h45
      rw [← terminalClearedIotaDefect610_leftJet_factored h0 w1 a41
        p32 s1 u2 b62 q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
        (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda]
      rw [hpowJetL]
      ring
    have hheadevalL :
        bridgeIotaLeftHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 := by
      have hev := congrArg (Polynomial.eval a) hpeelL
      have h5z : (0 : k) ^ 5 = 0 := by norm_num
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, hroot,
        bridgeIotaLeftHead610_eval, h5z, mul_zero, zero_mul,
        add_zero] at hev
      exact hev
    have hresL :=
      bridgeIota_left_residual610 (w1.eval a) (a41.eval a)
        (p31.eval a) (s1.eval a) (b62.eval a) ((p.coeff 2).eval a)
        (q41.eval a) lambda hheadevalL hp31z hMs hWform hUload
    exact Or.inl ⟨hp31z, p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform, hQ3form, hpeelL, hheadevalL, hresL⟩
  · exact Or.inr ⟨htp, hb62form,
      bridgeIota_comp_residual610 (w1.eval a) (a41.eval a)
        (p31.eval a) (s1.eval a) (u1.eval a) (b62.eval a)
        (q52.eval a) ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda
        hheadeval hMs hTu hVq hWq hUload hb62form⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing terminal integral bridge packet of a normalized
scale-two `(6,10)` nonzero face: the fifteenth final-row boundary data
`W E' - D X' = j ≠ 0` together with the weight-`50` power relation of
the degree-`5` first integral `ι`, its `h₀⁴⁴`-peeled head, the
chamber-free factored quotients, and the per-branch reductions — the
deeper `h₀⁴⁵` peel with
`a₄₁(a) (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0` on the `p₃₁(a) = 0`
sibling and `p₃₁(a)² (5 a₄₁² + 2 p₃₁ w₁)(a) = 0` on the complementary
factor.  The ground constant `iotaK` is preserved, not cleared. -/
theorem normalized610ScaleTwo_nonzeroFace_terminalIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK : K)
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
                a41.eval a * ((4 : K) * (a41.eval a) ^ 4 -
                    (35 : K) * (p.coeff 2).eval a *
                      (a41.eval a) ^ 2 +
                    (90 : K) * ((p.coeff 2).eval a) ^ 2) = 0) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            (p31.eval a) ^ 2 * ((5 : K) * (a41.eval a) ^ 2 +
              (2 : K) * p31.eval a * w1.eval a) = 0)) ∧
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', iotaK, hwN, ha4sN,
    hp3N, hsN, huN, hb6sN, hq5N, hMs', hTu', hVq', hWq', hUload',
    hrow, hroweval, hpow, hpeel, hheadeval, hres1, hres2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, w1', a41', s1', u1', p31', b62',
    q52', hh0, hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN,
    huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, hpow,
    hpeel, hheadeval, hres1, hres2, halt, hN'⟩

end NonzeroTerminalIntegralBridge610

#print axioms terminalIotaResidual610_deriv_zero
#print axioms nonzeroFace610_terminalIotaPowerRelation
#print axioms terminalClearedIotaDefect610_jet_factored
#print axioms terminalClearedIotaDefect610_leftJet_factored
#print axioms bridgeIota_chamberFree_residual610
#print axioms bridgeIota_uload_residual610
#print axioms bridgeIota_comp_residual610
#print axioms bridgeIota_left_residual610
#print axioms nonzeroFace610_linearRoot_terminalIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_terminalIntegralBridge

end Max11DegreeRoutes
