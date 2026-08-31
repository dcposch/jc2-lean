import Fable410ScaleTwoAlignedEighthFaceScratch

/-! # Ninth aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedEighthFaceScratch` consumed the degree-`4`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`27/2` first integral `M₁₄² = κ₈ H²⁷` of the ninth defect, the
five-deep square peel carrying `s₅` through `s₉`, the nonsquare septic
block tying `q₁` with an `H`-cofactor, and the nonsquare root pin
`g(a) f(a) + 8 p₁(a) = 0`.  This file consumes the next unused aligned
row, the degree-`3` Jacobian coefficient — the FIRST row that sees
`q₀`, and it sees it through `q₀'` ONLY: with `p₄ = H²` the
`p₄'`-pairing of the row carries the Y-weight `0 · q₀`, so the plain
letter `q₀` drops out of the literal row and only `4 p₄ q₀'` survives
(internal names `alignedTenth*`).

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` through degree-`4` brackets of `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, `M₁₂`, and `M₁₄`, the degree-`3` row is the weighted
derivative of the cleared tenth defect

`M₁₆ = 3932160 p₀ (p₁² + p₀ p₂) H¹⁴ - 4194304 q₀ H¹⁵
  - 983040 p₀² p₃² H¹² - 3932160 p₀ p₁ p₂ p₃ H¹² - 983040 p₁² p₂² H¹²
  - 655360 p₀ p₂³ H¹² - 655360 p₁³ p₃ H¹² + 983040 p₀ p₁ p₃³ H¹⁰
  + 1474560 p₀ p₂² p₃² H¹⁰ + 1474560 p₁² p₂ p₃² H¹⁰
  + 983040 p₁ p₂³ p₃ H¹⁰ + 49152 p₂⁵ H¹⁰ - 614400 p₀ p₂ p₃⁴ H⁸
  - 307200 p₁² p₃⁴ H⁸ - 1228800 p₁ p₂² p₃³ H⁸ - 307200 p₂⁴ p₃² H⁸
  + 71680 p₀ p₃⁶ H⁶ + 430080 p₁ p₂ p₃⁵ H⁶ + 358400 p₂³ p₃⁴ H⁶
  - 46080 p₁ p₃⁷ H⁴ - 161280 p₂² p₃⁶ H⁴ + 31680 p₂ p₃⁸ H² - 2288 p₃¹⁰
  + 524288 κ p₀² H¹⁵
  - p₃ M₁₄ - (16 p₂ H² - 4 p₃²) M₁₂ - (96 p₁ H⁴ - 24 p₂ p₃ H² + 5 p₃³) M₁₀
  - 2048 p₀ H⁶ M₈
  - (2560 p₀ p₃ H⁶ + 2560 p₁ p₂ H⁶ - 960 p₁ p₃² H⁴ - 960 p₂² p₃ H⁴
    + 560 p₂ p₃³ H² - 77 p₃⁵) M₆
  - (24576 p₀ p₂ H⁸ + 12288 p₁² H⁸ - 6144 p₀ p₃² H⁶ - 12288 p₁ p₂ p₃ H⁶
    - 2048 p₂³ H⁶ + 3072 p₁ p₃³ H⁴ + 4608 p₂² p₃² H⁴ - 1920 p₂ p₃⁴ H²
    + 224 p₃⁶) M₄
  - (344064 p₀ p₁ H¹⁰ - 86016 p₀ p₂ p₃ H⁸ - 43008 p₁² p₃ H⁸
    - 43008 p₁ p₂² H⁸ + 17920 p₀ p₃³ H⁶ + 53760 p₁ p₂ p₃² H⁶
    + 17920 p₂³ p₃ H⁶ - 10080 p₁ p₃⁴ H⁴ - 20160 p₂² p₃³ H⁴
    + 6552 p₂ p₃⁵ H² - 663 p₃⁷) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect whose head `3932160 p₀ (p₁² + p₀ p₂) H¹⁴` factors through `p₀`
times the p-discriminant block `p₁² + p₀ p₂`, the first whose
`κ`-module is the pure-`p₀` square `524288 κ p₀² H¹⁵`, and the first
whose `q`-letter enters at the FULL weight `q₀ H¹⁵` — via the exact
multiplier identity

`1048576 H¹⁴ · row₃[p₄ = H²] = (H M₁₆' - 15 M₁₆ H')
  + 2 p₃ (2 H M₁₄' - 27 M₁₄ H')
  + (8 p₃² + 32 p₂ H²) (H M₁₂' - 12 M₁₂ H')
  + (64 p₁ H⁴ + 48 p₂ p₃ H² - 2 p₃³) (2 H M₁₀' - 21 M₁₀ H')
  + (2048 p₀ H⁶ + 2048 p₁ p₃ H⁴ + 1024 p₂² H⁴) (H M₈' - 9 M₈ H')
  + (5120 p₀ p₃ H⁶ + 5120 p₁ p₂ H⁶ + 640 p₁ p₃² H⁴ + 640 p₂² p₃ H⁴
    - 160 p₂ p₃³ H² + 14 p₃⁵) (2 H M₆' - 15 M₆ H')
  + (49152 p₀ p₂ H⁸ + 24576 p₁² H⁸ + 12288 p₀ p₃² H⁶ + 24576 p₁ p₂ p₃ H⁶
    + 4096 p₂³ H⁶ - 2048 p₁ p₃³ H⁴ - 3072 p₂² p₃² H⁴ + 768 p₂ p₃⁴ H²
    - 64 p₃⁶) (H M₄' - 6 M₄ H')
  + (229376 p₀ p₁ H¹⁰ + 172032 p₀ p₂ p₃ H⁸ + 86016 p₁² p₃ H⁸
    + 86016 p₁ p₂² H⁸ - 7168 p₀ p₃³ H⁶ - 21504 p₁ p₂ p₃² H⁶
    - 7168 p₂³ p₃ H⁶ + 2240 p₁ p₃⁴ H⁴ + 4480 p₂² p₃³ H⁴
    - 1008 p₂ p₃⁵ H² + 78 p₃⁷) (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁰ H¹⁴` (unique solution of the factored cofactor
system, nullspace exactly one).  The correction module is EMPTY for the
FOURTH row in a row: neither the aligned-face residual `N` nor the
degree-`11` relation `R` appears — the row's letters stop at `q₄`, so
no bracket combination can carry `q₈` or `q₉`.  On the aligned face
every previous bracket vanishes, so `H M₁₆' = 15 M₁₆ H'` and the
weight-`15` first integral

`M₁₆ = κ₉ H¹⁵`

holds for a preserved constant `κ₉` — even-type and CHAMBER-FREE, the
FIFTH rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵`; no parity kill,
`κ₉` is preserved in BOTH chambers.  The chamber core, after cancelling
`h₀²⁰` resp. `H¹⁰`, is a QUARTIC-cofactor cube plus a `p₁`-loaded
square block:

`16 (143 w⁴ - 264 p₂ w² + 48 p₂²) (w² - 4 p₂)³
  + 15360 h p₁ w (3 w² - 4 p₂) (w² - 4 p₂)²`  (`h = h₀²` resp. `H`)

— the first aligned chamber core whose odd cofactor
`143 w⁴ - 264 p₂ w² + 48 p₂²` does not factor against the quadratic
kill (it evaluates to `80 w⁴` on `w² = 4 p₂`).

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
  `M₁₄ = μ₄ h₀²⁷`, `M₁₆ = κ₉ H¹⁵`: on the consumed divisibility
  `u² - 4 p₂ = h₀ v` the peel is SEVEN deep — the deepest aligned peel
  so far (`q₀` sits ten levels above the core against the
  divisibility's three): the NEW μ-loaded SEPTIC divisibility
  `16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
  + 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀` — self-similar to the
  sixth-, seventh-, and eighth-face divisibilities one level down —
  then the explicit peels producing `s₁₁` through `s₁₆` (`s₁₅` is the
  FIRST peel letter loaded with `μ₄`), and the solved row

  `4194304 q₀ = 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - s₁₆`

  — the FIRST aligned solved row with NO `h₀`-suppressed tail at all:
  `q₀` carries no `h₀` factor, `κ₉` enters at level ZERO, and every
  higher letter is absorbed into the peel.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₈ = κ₅ H⁹`,
  `M₁₂ = κ₇ H¹²`, `M₁₆ = κ₉ H¹⁵`: on the consumed divisibility
  `g² - 4 p₂ = H f` the row does NOT solve — the octic block identity
  `16 (143 g⁴ - 264 p₂ g² + 48 p₂²) f³ + 15360 p₁ g (3 g² - 4 p₂) f²
  + 245760 p₁² g² f + 655360 p₁³ g
  = H · (((61440 p₀ - 192 κ₃) g² - 61440 p₁²) f²
  + (983040 p₀ - 3072 κ₃) g p₁ f + (3932160 p₀ - 12288 κ₃) p₁²
  + H · ((10240 p₀ - 32 κ₃) f³ + (6144 κ₃ p₀ + 4 κ₇ - 983040 p₀²) f
  + 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - 4194304 q₀))` consumes `q₀` with
  an `H²`-cofactor — the first aligned letter tied TWO `H`-levels deep.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie `1280 u(a)⁴ v(a)³ = 5 μ u(a)⁷`, whose clash with the
sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a
factor-`555` mismatch, `560 μ u⁷` against `5 μ u⁷`) RE-DERIVES the
root dichotomy `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`; on it
`s₁₀(a) = 0` unconditionally, and the ties
`s₁₀(a) = -30720 p₁ u³ v²`,
`s₁₁(a) = -245760 p₁² u² v - 672 μ p₁ u⁴ - 3 μ₂ u⁵`,
`s₁₅(a) = (6144 κ₃ p₀ + 4 κ₇ - 983040 p₀²) v - 344064 μ p₀ p₁
- 2560 μ₂ p₀ u - 96 μ₃ p₁ - μ₄ u` — the FIRST aligned root tie loaded
with `μ₄` — and the `q₀` value tie
`4194304 q₀(a) = 524288 κ p₀(a)² - 2048 κ₅ p₀(a) - κ₉ - s₁₆(a)` — the
first aligned root tie that sees `κ₉` — follow.  The nonsquare
chamber's octic block dies at `a` and collapses on the quadratic kill
to the PERFECT-CUBE PRODUCT

`g(a) · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content as
a product kill (this row alone forces `g(a) = 0` or the pin; no new pin
is claimed beyond the eighth face's).  `q₀` itself is `H`-suppressed
twice at the root and stays free there.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`,
`natDegree_one_dvd_of_root_kill_410`, the fourth-face square descent
`p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, the sixth-face divisibility carrying `s`, and the
chamber form/kill quotients of the odd rows.  The weight-`15` Wronskian
quotient `fifteenthPowerRelation_of_weightFifteenRow_410` is new but
generic (even-type, distinct from the odd-type
`fifteenthPowerRelation_of_weightFifteenHalfRow_410`).

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₁₀ = 0`, `μ = 0` through `μ₄ = 0`, `κ = 0` through
`κ₉ = 0`) are not excluded, and the constants are preserved where not
previously forced (`κ₄ = κ₆ = κ₈ = 0` remain forced in the nonsquare
chamber only; `κ₉` is preserved in both).  `p₀, p₁, p₂` are
constrained only through the solved forms, the divisibilities, and the
root ties.  The aligned Jacobian tower now has TWO unused rows left:
the degree-`2` row (seeing `q₀` and `q₁` through derivatives and
values) and the degree-`1`/degree-`0` tail; the next unused aligned
row is the degree-`2` Jacobian coefficient.  No total-degree or
twice-prime theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`3` Keller coefficient on the aligned face -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`3` Jacobian coefficient, the first
aligned row that sees `q₀` — through its derivative only, since the
`p₄'`-pairing carries Y-weight `0 · q₀`.  It is derived directly from
the Keller bracket. -/
theorem alignedTenthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 3) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (3 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4]
  linear_combination hcoeff

/-! ## Aligned tenth defect -/

/-- Cleared tenth defect of the degree-`3` aligned `(4,10)` row, kept
in factored form through the third through ninth defects `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, `M₁₂`, and `M₁₄`.  Every monomial has exact
`H`-weight `15`; the head is `3932160 p₀ (p₁² + p₀ p₂) H¹⁴`, the
`κ`-module is the single pure-`p₀` term `524288 κ p₀² H¹⁵`, and the
new letter enters at full weight as `-4194304 q₀ H¹⁵`. -/
def alignedTenthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (3932160 : K[X]) * a0 * a1 ^ 2 * H ^ 14 +
    (3932160 : K[X]) * a0 ^ 2 * a2 * H ^ 14 -
    (4194304 : K[X]) * b0 * H ^ 15 -
    (983040 : K[X]) * a0 ^ 2 * a3 ^ 2 * H ^ 12 -
    (3932160 : K[X]) * a0 * a1 * a2 * a3 * H ^ 12 -
    (983040 : K[X]) * a1 ^ 2 * a2 ^ 2 * H ^ 12 -
    (655360 : K[X]) * a0 * a2 ^ 3 * H ^ 12 -
    (655360 : K[X]) * a1 ^ 3 * a3 * H ^ 12 +
    (983040 : K[X]) * a0 * a1 * a3 ^ 3 * H ^ 10 +
    (1474560 : K[X]) * a0 * a2 ^ 2 * a3 ^ 2 * H ^ 10 +
    (1474560 : K[X]) * a1 ^ 2 * a2 * a3 ^ 2 * H ^ 10 +
    (983040 : K[X]) * a1 * a2 ^ 3 * a3 * H ^ 10 +
    (49152 : K[X]) * a2 ^ 5 * H ^ 10 -
    (614400 : K[X]) * a0 * a2 * a3 ^ 4 * H ^ 8 -
    (307200 : K[X]) * a1 ^ 2 * a3 ^ 4 * H ^ 8 -
    (1228800 : K[X]) * a1 * a2 ^ 2 * a3 ^ 3 * H ^ 8 -
    (307200 : K[X]) * a2 ^ 4 * a3 ^ 2 * H ^ 8 +
    (71680 : K[X]) * a0 * a3 ^ 6 * H ^ 6 +
    (430080 : K[X]) * a1 * a2 * a3 ^ 5 * H ^ 6 +
    (358400 : K[X]) * a2 ^ 3 * a3 ^ 4 * H ^ 6 -
    (46080 : K[X]) * a1 * a3 ^ 7 * H ^ 4 -
    (161280 : K[X]) * a2 ^ 2 * a3 ^ 6 * H ^ 4 +
    (31680 : K[X]) * a2 * a3 ^ 8 * H ^ 2 - (2288 : K[X]) * a3 ^ 10 +
    Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2 * H ^ 15) -
    a3 * alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((16 : K[X]) * a2 * H ^ 2 - (4 : K[X]) * a3 ^ 2) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    ((96 : K[X]) * a1 * H ^ 4 - (24 : K[X]) * a2 * a3 * H ^ 2 +
      (5 : K[X]) * a3 ^ 3) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    (2048 : K[X]) * a0 * H ^ 6 *
      alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ -
    ((2560 : K[X]) * a0 * a3 * H ^ 6 + (2560 : K[X]) * a1 * a2 * H ^ 6 -
      (960 : K[X]) * a1 * a3 ^ 2 * H ^ 4 -
      (960 : K[X]) * a2 ^ 2 * a3 * H ^ 4 +
      (560 : K[X]) * a2 * a3 ^ 3 * H ^ 2 - (77 : K[X]) * a3 ^ 5) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((24576 : K[X]) * a0 * a2 * H ^ 8 + (12288 : K[X]) * a1 ^ 2 * H ^ 8 -
      (6144 : K[X]) * a0 * a3 ^ 2 * H ^ 6 -
      (12288 : K[X]) * a1 * a2 * a3 * H ^ 6 -
      (2048 : K[X]) * a2 ^ 3 * H ^ 6 +
      (3072 : K[X]) * a1 * a3 ^ 3 * H ^ 4 +
      (4608 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 -
      (1920 : K[X]) * a2 * a3 ^ 4 * H ^ 2 + (224 : K[X]) * a3 ^ 6) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((344064 : K[X]) * a0 * a1 * H ^ 10 -
      (86016 : K[X]) * a0 * a2 * a3 * H ^ 8 -
      (43008 : K[X]) * a1 ^ 2 * a3 * H ^ 8 -
      (43008 : K[X]) * a1 * a2 ^ 2 * H ^ 8 +
      (17920 : K[X]) * a0 * a3 ^ 3 * H ^ 6 +
      (53760 : K[X]) * a1 * a2 * a3 ^ 2 * H ^ 6 +
      (17920 : K[X]) * a2 ^ 3 * a3 * H ^ 6 -
      (10080 : K[X]) * a1 * a3 ^ 4 * H ^ 4 -
      (20160 : K[X]) * a2 ^ 2 * a3 ^ 3 * H ^ 4 +
      (6552 : K[X]) * a2 * a3 ^ 5 * H ^ 2 - (663 : K[X]) * a3 ^ 7) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`3` Jacobian expression with the
weight-`15` bracket of `M₁₆`.  The only corrections are the consumed
degree-`10` through degree-`4` brackets of `M₂`, `M₄`, `M₆`, `M₈`,
`M₁₀`, `M₁₂`, and `M₁₄`: neither the aligned-face residual `N` nor the
degree-`11` relation `R` appears at all — the correction module is
empty for the fourth row in a row.  Every correction vanishes on the
aligned face. -/
theorem alignedTenthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (1048576 : K[X]) * H ^ 14 *
        (a3.derivative * b1 +
          a2.derivative * (b2 * (2 : K[X])) +
          a1.derivative * (b3 * (3 : K[X])) +
          a0.derivative * (b4 * (4 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b0.derivative +
          (a3 * (3 : K[X])) * b1.derivative +
          (a2 * (2 : K[X])) * b2.derivative +
          a1 * b3.derivative)) =
      (H *
          (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (15 : K[X]) *
          alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (2 : K[X]) * a3 *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((8 : K[X]) * a3 ^ 2 + (32 : K[X]) * a2 * H ^ 2) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((64 : K[X]) * a1 * H ^ 4 + (48 : K[X]) * a2 * a3 * H ^ 2 -
            (2 : K[X]) * a3 ^ 3) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((2048 : K[X]) * a0 * H ^ 6 + (2048 : K[X]) * a1 * a3 * H ^ 4 +
            (1024 : K[X]) * a2 ^ 2 * H ^ 4) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((5120 : K[X]) * a0 * a3 * H ^ 6 + (5120 : K[X]) * a1 * a2 * H ^ 6 +
            (640 : K[X]) * a1 * a3 ^ 2 * H ^ 4 +
            (640 : K[X]) * a2 ^ 2 * a3 * H ^ 4 -
            (160 : K[X]) * a2 * a3 ^ 3 * H ^ 2 + (14 : K[X]) * a3 ^ 5) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((49152 : K[X]) * a0 * a2 * H ^ 8 + (24576 : K[X]) * a1 ^ 2 * H ^ 8 +
            (12288 : K[X]) * a0 * a3 ^ 2 * H ^ 6 +
            (24576 : K[X]) * a1 * a2 * a3 * H ^ 6 +
            (4096 : K[X]) * a2 ^ 3 * H ^ 6 -
            (2048 : K[X]) * a1 * a3 ^ 3 * H ^ 4 -
            (3072 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 +
            (768 : K[X]) * a2 * a3 ^ 4 * H ^ 2 - (64 : K[X]) * a3 ^ 6) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((229376 : K[X]) * a0 * a1 * H ^ 10 +
            (172032 : K[X]) * a0 * a2 * a3 * H ^ 8 +
            (86016 : K[X]) * a1 ^ 2 * a3 * H ^ 8 +
            (86016 : K[X]) * a1 * a2 ^ 2 * H ^ 8 -
            (7168 : K[X]) * a0 * a3 ^ 3 * H ^ 6 -
            (21504 : K[X]) * a1 * a2 * a3 ^ 2 * H ^ 6 -
            (7168 : K[X]) * a2 ^ 3 * a3 * H ^ 6 +
            (2240 : K[X]) * a1 * a3 ^ 4 * H ^ 4 +
            (4480 : K[X]) * a2 ^ 2 * a3 ^ 3 * H ^ 4 -
            (1008 : K[X]) * a2 * a3 ^ 5 * H ^ 2 + (78 : K[X]) * a3 ^ 7) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [alignedTenthDefect410, alignedNinthDefect410,
    alignedEighthDefect410, alignedSeventhDefect410, alignedSixthDefect410,
    alignedFifthDefect410, alignedFourthDefect410, alignedThirdDefect410,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face, with the consumed degree-`11` through
degree-`4` rows, the degree-`3` row is the weighted derivative
`H M₁₆' - 15 M₁₆ H' = 0`. -/
theorem alignedTenthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (15 : K[X]) *
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedTenthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4] at hrow
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB8 :=
    alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB10 :=
    alignedSeventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB12 :=
    alignedEighthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB14 :=
    alignedNinthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedTenthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 0)
    (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12, hB14] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-`15` polynomial first integral -/

/-- Generic Wronskian quotient for the weight-`15` bracket: over a
characteristic-zero field, `H D' - 15 D H' = 0` forces
`D = C c * H¹⁵`.  Even-type: no squaring, no parity split — distinct
from the odd-type half-integral quotient
`fifteenthPowerRelation_of_weightFifteenHalfRow_410`. -/
theorem fifteenthPowerRelation_of_weightFifteenRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (15 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 15 := by
  have hC15 : Polynomial.C (15 : K) = (15 : K[X]) :=
    Polynomial.C_eq_natCast 15
  have hW : Polynomial.wronskian D (H ^ 15) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (15 : K) * H ^ (15 - 1) * H.derivative) -
          D.derivative * H ^ 15 =
          H ^ 14 *
            (Polynomial.C (15 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC15]
        have hfac :
            (15 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 15 hH) hW

/-- Weight-fifteen polynomial first integral of the aligned `(4,10)`
tenth defect: `M₁₆ = κ₉ H¹⁵` — even-type and chamber-free, the fifth
rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵`, one level below the
odd twenty-seventh-power shape of the degree-`4` row. -/
theorem alignedTenthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₉ : K,
      alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₉ * H ^ 15 :=
  fifteenthPowerRelation_of_weightFifteenRow_410 hH
    (alignedTenthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared square-core form of the tenth defect relation: cancelling
`h₀²⁰` from `M₁₆ = κ₉ H¹⁵` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
`M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) (u² - 4 p₂)³
+ 15360 h₀² p₁ u (3 u² - 4 p₂) (u² - 4 p₂)²` carried by `h₀³` against
the explicit quotient, whose leading block is the μ-loaded septic
`663 u⁷ - 6552 p₂ u⁵ + 20160 p₂² u³ - 17920 p₂³ u`. -/
theorem alignedSquareTenth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27)
    (hM16 : alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₉ * H ^ 15) :
    (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (15360 : K[X]) * h0 ^ 2 * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
              (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
              (17920 : K[X]) * a2 ^ 3 * u) +
          h0 * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
              (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                u ^ 2 - (61440 : K[X]) * a1 ^ 2) *
              (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (245760 : K[X]) * a1 ^ 2 * u ^ 2 *
              (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 *
            (Polynomial.C μ *
                (a1 * ((10080 : K[X]) * u ^ 4 -
                  (53760 : K[X]) * a2 * u ^ 2 +
                  (43008 : K[X]) * a2 ^ 2)) +
              Polynomial.C μ₂ *
                (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
                  (960 : K[X]) * a2 ^ 2))) +
          h0 ^ 3 *
            (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 * u * (u ^ 2 - (4 : K[X]) * a2) -
              (655360 : K[X]) * a1 ^ 3 * u) +
          h0 ^ 4 *
            (Polynomial.C μ *
                ((86016 : K[X]) * a0 * a2 * u -
                  (17920 : K[X]) * a0 * u ^ 3 +
                  (43008 : K[X]) * a1 ^ 2 * u) +
              Polynomial.C μ₂ *
                ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
              Polynomial.C μ₃ *
                ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3)) +
          h0 ^ 5 *
            (((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
                a1 ^ 2 +
              (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                Polynomial.C κ₇ * (4 : K[X]) -
                (983040 : K[X]) * a0 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2)) -
          h0 ^ 6 *
            (Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
              Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
              Polynomial.C μ₃ * ((96 : K[X]) * a1) +
              Polynomial.C μ₄ * u) +
          h0 ^ 7 *
            (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
              Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
              Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  have hM16' := hM16
  simp only [alignedTenthDefect410] at hM16'
  rw [hM14, hM12, hM10, hM8, hM6, hM4, hM2, hHsq, hp3] at hM16'
  apply mul_left_cancel₀ (pow_ne_zero 20 hh0)
  linear_combination -hM16'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`3` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains `h₀³`,
and the peel is SEVEN deep: the NEW μ-loaded septic divisibility
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
+ 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀` — self-similar to the sixth-,
seventh-, and eighth-face divisibilities one level down — then the
explicit peels producing `s₁₁` through `s₁₆` (`s₁₅` is the first peel
letter loaded with `μ₄`), and the solved row with NO `h₀`-suppressed
tail: `q₀` carries no `h₀` factor and `κ₉` enters at level zero. -/
theorem alignedSquareTenth_solved_410 {K : Type*} [Field K] [CharZero K]
    {h0 u v a0 a1 a2 b0 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
              (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (15360 : K[X]) * h0 ^ 2 * a1 * u *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
                (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
                (17920 : K[X]) * a2 ^ 3 * u) +
            h0 * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                  u ^ 2 - (61440 : K[X]) * a1 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (245760 : K[X]) * a1 ^ 2 * u ^ 2 *
                (u ^ 2 - (4 : K[X]) * a2)) +
            h0 ^ 2 *
              (Polynomial.C μ *
                  (a1 * ((10080 : K[X]) * u ^ 4 -
                    (53760 : K[X]) * a2 * u ^ 2 +
                    (43008 : K[X]) * a2 ^ 2)) +
                Polynomial.C μ₂ *
                  (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
                    (960 : K[X]) * a2 ^ 2))) +
            h0 ^ 3 *
              (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                  a1 * u * (u ^ 2 - (4 : K[X]) * a2) -
                (655360 : K[X]) * a1 ^ 3 * u) +
            h0 ^ 4 *
              (Polynomial.C μ *
                  ((86016 : K[X]) * a0 * a2 * u -
                    (17920 : K[X]) * a0 * u ^ 3 +
                    (43008 : K[X]) * a1 ^ 2 * u) +
                Polynomial.C μ₂ *
                  ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
                Polynomial.C μ₃ *
                  ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3)) +
            h0 ^ 5 *
              (((3932160 : K[X]) * a0 -
                  Polynomial.C κ₃ * (12288 : K[X])) * a1 ^ 2 +
                (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                  Polynomial.C κ₇ * (4 : K[X]) -
                  (983040 : K[X]) * a0 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2)) -
            h0 ^ 6 *
              (Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
                Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
                Polynomial.C μ₃ * ((96 : K[X]) * a1) +
                Polynomial.C μ₄ * u) +
            h0 ^ 7 *
              (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
                Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
                Polynomial.C κ₉ - (4194304 : K[X]) * b0)))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₁₀ s₁₁ s₁₂ s₁₃ s₁₄ s₁₅ s₁₆ : K[X],
      (16 : K[X]) * ((143 : K[X]) * u ^ 4 - (264 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * v ^ 3 -
          Polynomial.C μ *
            ((663 : K[X]) * u ^ 7 - (6552 : K[X]) * a2 * u ^ 5 +
              (20160 : K[X]) * a2 ^ 2 * u ^ 3 -
              (17920 : K[X]) * a2 ^ 3 * u) = h0 * s₁₀ ∧
      s₁₀ + (15360 : K[X]) * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 = h0 * s₁₁ ∧
      s₁₁ + (245760 : K[X]) * a1 ^ 2 * u ^ 2 * v -
          Polynomial.C μ *
            (a1 * ((10080 : K[X]) * u ^ 4 - (53760 : K[X]) * a2 * u ^ 2 +
              (43008 : K[X]) * a2 ^ 2)) -
          Polynomial.C μ₂ *
            (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
              (960 : K[X]) * a2 ^ 2)) = h0 * s₁₂ ∧
      s₁₂ - (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
            u ^ 2 - (61440 : K[X]) * a1 ^ 2) * v ^ 2 +
          (655360 : K[X]) * a1 ^ 3 * u = h0 * s₁₃ ∧
      s₁₃ - ((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            v ^ 3 -
          ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            a1 * u * v -
          Polynomial.C μ *
            ((86016 : K[X]) * a0 * a2 * u - (17920 : K[X]) * a0 * u ^ 3 +
              (43008 : K[X]) * a1 ^ 2 * u) -
          Polynomial.C μ₂ *
            ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) -
          Polynomial.C μ₃ *
            ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3) = h0 * s₁₄ ∧
      s₁₄ - ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 = h0 * s₁₅ ∧
      s₁₅ - (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
            Polynomial.C κ₇ * (4 : K[X]) -
            (983040 : K[X]) * a0 ^ 2) * v +
          Polynomial.C μ * ((344064 : K[X]) * a0 * a1) +
          Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) +
          Polynomial.C μ₃ * ((96 : K[X]) * a1) +
          Polynomial.C μ₄ * u = h0 * s₁₆ ∧
      (4194304 : K[X]) * b0 =
        Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
          Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
          Polynomial.C κ₉ - s₁₆ := by
  obtain ⟨s₁₆, hs₁₆⟩ : ∃ w : K[X],
      w = Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
        Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
        Polynomial.C κ₉ - (4194304 : K[X]) * b0 := ⟨_, rfl⟩
  obtain ⟨s₁₅, hs₁₅⟩ : ∃ w : K[X],
      w = (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
          Polynomial.C κ₇ * (4 : K[X]) - (983040 : K[X]) * a0 ^ 2) * v -
        Polynomial.C μ * ((344064 : K[X]) * a0 * a1) -
        Polynomial.C μ₂ * ((2560 : K[X]) * a0 * u) -
        Polynomial.C μ₃ * ((96 : K[X]) * a1) -
        Polynomial.C μ₄ * u + h0 * s₁₆ := ⟨_, rfl⟩
  obtain ⟨s₁₄, hs₁₄⟩ : ∃ w : K[X],
      w = ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 + h0 * s₁₅ := ⟨_, rfl⟩
  obtain ⟨s₁₃, hs₁₃⟩ : ∃ w : K[X],
      w = ((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) * v ^ 3 +
        ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          a1 * u * v +
        Polynomial.C μ *
          ((86016 : K[X]) * a0 * a2 * u - (17920 : K[X]) * a0 * u ^ 3 +
            (43008 : K[X]) * a1 ^ 2 * u) +
        Polynomial.C μ₂ *
          ((960 : K[X]) * a1 * u ^ 2 - (2560 : K[X]) * a1 * a2) +
        Polynomial.C μ₃ * ((24 : K[X]) * a2 * u - (5 : K[X]) * u ^ 3) +
        h0 * s₁₄ := ⟨_, rfl⟩
  obtain ⟨s₁₂, hs₁₂⟩ : ∃ w : K[X],
      w = (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
          u ^ 2 - (61440 : K[X]) * a1 ^ 2) * v ^ 2 -
        (655360 : K[X]) * a1 ^ 3 * u + h0 * s₁₃ := ⟨_, rfl⟩
  obtain ⟨s₁₁, hs₁₁⟩ : ∃ w : K[X],
      w = -(245760 : K[X]) * a1 ^ 2 * u ^ 2 * v +
        Polynomial.C μ *
          (a1 * ((10080 : K[X]) * u ^ 4 - (53760 : K[X]) * a2 * u ^ 2 +
            (43008 : K[X]) * a2 ^ 2)) +
        Polynomial.C μ₂ *
          (u * ((77 : K[X]) * u ^ 4 - (560 : K[X]) * a2 * u ^ 2 +
            (960 : K[X]) * a2 ^ 2)) + h0 * s₁₂ := ⟨_, rfl⟩
  obtain ⟨s₁₀, hs₁₀⟩ : ∃ w : K[X],
      w = -(15360 : K[X]) * a1 * u *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 2 +
        h0 * s₁₁ := ⟨_, rfl⟩
  refine ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs₁₀, hs₁₁, hs₁₂, hs₁₃, hs₁₄, hs₁₅, hs₁₆]
    linear_combination hcore
  · rw [hs₁₀]
    ring
  · rw [hs₁₁]
    ring
  · rw [hs₁₂]
    ring
  · rw [hs₁₃]
    ring
  · rw [hs₁₄]
    ring
  · rw [hs₁₅]
    ring
  · rw [hs₁₆]
    ring

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared nonsquare-core form of the tenth defect relation:
cancelling `H¹⁰` from `M₁₆ = κ₉ H¹⁵` on `p₃ = H g`, `M₂ = 0`,
`M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`, `M₁₀ = 0`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = 0` exposes the same core in `g` carried by `H²` against the
explicit quotient — no parity kill: `κ₉` survives the nonsquare
chamber. -/
theorem alignedNonsquareTenth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM16 : alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₉ * H ^ 15) :
    (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (15360 : K[X]) * H * a1 * g *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
              g ^ 2 - (61440 : K[X]) * a1 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
          (245760 : K[X]) * a1 ^ 2 * g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) +
          H * (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
              g * a1 * (g ^ 2 - (4 : K[X]) * a2) -
            (655360 : K[X]) * a1 ^ 3 * g) +
          H ^ 2 *
            (((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
                a1 ^ 2 +
              (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                Polynomial.C κ₇ * (4 : K[X]) -
                (983040 : K[X]) * a0 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2)) +
          H ^ 3 *
            (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
              Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
              Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  have hM16' := hM16
  simp only [alignedTenthDefect410] at hM16'
  rw [hM140, hM12, hM100, hM8, hM60, hM4, hM20, hg] at hM16'
  apply mul_left_cancel₀ (pow_ne_zero 10 hH)
  linear_combination -hM16'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`3` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` of the fifth face the row does NOT
solve — the octic block
`16 (143 g⁴ - 264 p₂ g² + 48 p₂²) f³ + 15360 p₁ g (3 g² - 4 p₂) f²
+ 245760 p₁² g² f + 655360 p₁³ g` is an exact `H`-multiple of the
explicit quotient, and `q₀` sits in its `H²`-part — the first aligned
letter consumed with an `H²`-cofactor (tied two levels deep, not
solved). -/
theorem alignedNonsquareTenth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 b0 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ : K}
    (hH : H ≠ 0)
    (hcore :
      (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
              (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (15360 : K[X]) * H * a1 * g *
            ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
              (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
                g ^ 2 - (61440 : K[X]) * a1 ^ 2) *
              (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (245760 : K[X]) * a1 ^ 2 * g ^ 2 *
              (g ^ 2 - (4 : K[X]) * a2) +
            H * (((983040 : K[X]) * a0 -
                Polynomial.C κ₃ * (3072 : K[X])) *
                g * a1 * (g ^ 2 - (4 : K[X]) * a2) -
              (655360 : K[X]) * a1 ^ 3 * g) +
            H ^ 2 *
              (((3932160 : K[X]) * a0 -
                  Polynomial.C κ₃ * (12288 : K[X])) * a1 ^ 2 +
                (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
                  Polynomial.C κ₇ * (4 : K[X]) -
                  (983040 : K[X]) * a0 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2)) +
            H ^ 3 *
              (Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
                Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
                Polynomial.C κ₉ - (4194304 : K[X]) * b0)))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (16 : K[X]) * ((143 : K[X]) * g ^ 4 - (264 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * f ^ 3 +
        (15360 : K[X]) * a1 * g *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) * f ^ 2 +
        (245760 : K[X]) * a1 ^ 2 * g ^ 2 * f +
        (655360 : K[X]) * a1 ^ 3 * g =
      H * ((((61440 : K[X]) * a0 - Polynomial.C κ₃ * (192 : K[X])) *
            g ^ 2 - (61440 : K[X]) * a1 ^ 2) * f ^ 2 +
        ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          g * a1 * f +
        ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 ^ 2 +
        H * (((10240 : K[X]) * a0 - Polynomial.C κ₃ * (32 : K[X])) *
            f ^ 3 +
          (Polynomial.C κ₃ * ((6144 : K[X]) * a0) +
            Polynomial.C κ₇ * (4 : K[X]) -
            (983040 : K[X]) * a0 ^ 2) * f +
          Polynomial.C κ * ((524288 : K[X]) * a0 ^ 2) -
          Polynomial.C κ₅ * ((2048 : K[X]) * a0) -
          Polynomial.C κ₉ - (4194304 : K[X]) * b0)) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing tenth-row packets -/

/-- Source-facing weight-`15` integral of a normalized aligned
scale-two `(4,10)` source: the degree-`3` row is consumed into
`M₁₆ = κ₉ H¹⁵` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedTenthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₆ * H ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        ∀ a : K, H.eval a = 0 →
          (p.coeff 3).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₄, hM6⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₅, hM8⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₆, hM10⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₇, hM12⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14, hM16,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber tenth packet of a normalized aligned scale-two
`(4,10)` source: the identifying chamber data, the chamber-free form
`M₁₆ = κ₉ H¹⁵`, the NEW μ-loaded septic divisibility
`16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
+ 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀`, the explicit peels producing
`s₁₁` through `s₁₆`, and the solved row with no `h₀`-suppressed tail.
The constants `μ`, `κ₃`, `μ₂`, `κ₅`, `μ₃`, `κ₇`, `μ₄`, and `κ₉` are
preserved, not cleared. -/
theorem normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ : K)
      (u v s₁₀ s₁₁ s₁₂ s₁₃ s₁₄ s₁₅ s₁₆ : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₂ * h0 ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C μ₃ * h0 ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₄ * h0 ^ 27 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (16 : K[X]) * ((143 : K[X]) * u ^ 4 -
              (264 : K[X]) * p.coeff 2 * u ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
            Polynomial.C μ *
              ((663 : K[X]) * u ^ 7 -
                (6552 : K[X]) * p.coeff 2 * u ^ 5 +
                (20160 : K[X]) * p.coeff 2 ^ 2 * u ^ 3 -
                (17920 : K[X]) * p.coeff 2 ^ 3 * u) = h0 * s₁₀ ∧
        s₁₀ + (15360 : K[X]) * p.coeff 1 * u *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) * v ^ 2 =
          h0 * s₁₁ ∧
        s₁₁ + (245760 : K[X]) * p.coeff 1 ^ 2 * u ^ 2 * v -
            Polynomial.C μ *
              (p.coeff 1 * ((10080 : K[X]) * u ^ 4 -
                (53760 : K[X]) * p.coeff 2 * u ^ 2 +
                (43008 : K[X]) * p.coeff 2 ^ 2)) -
            Polynomial.C μ₂ *
              (u * ((77 : K[X]) * u ^ 4 -
                (560 : K[X]) * p.coeff 2 * u ^ 2 +
                (960 : K[X]) * p.coeff 2 ^ 2)) = h0 * s₁₂ ∧
        s₁₂ - (((61440 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (192 : K[X])) * u ^ 2 -
              (61440 : K[X]) * p.coeff 1 ^ 2) * v ^ 2 +
            (655360 : K[X]) * p.coeff 1 ^ 3 * u = h0 * s₁₃ ∧
        s₁₃ - ((10240 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (32 : K[X])) * v ^ 3 -
            ((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * p.coeff 1 * u * v -
            Polynomial.C μ *
              ((86016 : K[X]) * p.coeff 0 * p.coeff 2 * u -
                (17920 : K[X]) * p.coeff 0 * u ^ 3 +
                (43008 : K[X]) * p.coeff 1 ^ 2 * u) -
            Polynomial.C μ₂ *
              ((960 : K[X]) * p.coeff 1 * u ^ 2 -
                (2560 : K[X]) * p.coeff 1 * p.coeff 2) -
            Polynomial.C μ₃ *
              ((24 : K[X]) * p.coeff 2 * u - (5 : K[X]) * u ^ 3) =
          h0 * s₁₄ ∧
        s₁₄ - ((3932160 : K[X]) * p.coeff 0 -
            Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 ^ 2 =
          h0 * s₁₅ ∧
        s₁₅ - (Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0) +
              Polynomial.C κ₇ * (4 : K[X]) -
              (983040 : K[X]) * p.coeff 0 ^ 2) * v +
            Polynomial.C μ * ((344064 : K[X]) * p.coeff 0 * p.coeff 1) +
            Polynomial.C μ₂ * ((2560 : K[X]) * p.coeff 0 * u) +
            Polynomial.C μ₃ * ((96 : K[X]) * p.coeff 1) +
            Polynomial.C μ₄ * u = h0 * s₁₆ ∧
        (4194304 : K[X]) * q.coeff 0 =
          Polynomial.C κ * ((524288 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ₅ * ((2048 : K[X]) * p.coeff 0) -
            Polynomial.C κ₉ - s₁₆ := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hDform⟩ :=
    ninthPower_squareChamber_form_410 hH hHsq hrel
  have hdeg1 : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hHdegree, Polynomial.natDegree_pow] at hdegree
    omega
  have hkill0 : ∀ a : K, h0.eval a = 0 → (p.coeff 3).eval a = 0 := by
    intro a ha
    apply alignedThird_rootKill_p3_410 hrel
    rw [hHsq]
    simp only [Polynomial.eval_pow, ha]
    norm_num
  obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
  obtain ⟨u, hu, _hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
  have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
    fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
  obtain ⟨v, hv, _hq4⟩ := alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
    twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14rel⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
    twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore10 :=
    alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form hM16
  obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, hd1, hd2, hd3, hd4, hd5,
    hd6, hd7, hq0⟩ := alignedSquareTenth_solved_410 hh0 hcore10 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, u, v, s₁₀, s₁₁, s₁₂, s₁₃,
    s₁₄, s₁₅, s₁₆, hp3, hDform, hM4, hM6form, hM8form, hM10form,
    hM12form, hM14form, hM16, hv, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hq0⟩

/-- Exact nonsquare-chamber tenth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free form `M₁₆ = κ₉ H¹⁵` (no parity kill at this row), and the
octic-block descent on the fifth face's divisibility `g² - 4 p₂ = H f`:
`q₀` is consumed with an `H²`-cofactor inside the explicit quotient —
tied two levels deep, not solved. -/
theorem normalized410ScaleTwo_alignedTenthRow_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g f : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((16 : K[X]) * ((143 : K[X]) * g ^ 4 -
              (264 : K[X]) * p.coeff 2 * g ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * f ^ 3 +
            (15360 : K[X]) * p.coeff 1 * g *
              ((3 : K[X]) * g ^ 2 - (4 : K[X]) * p.coeff 2) * f ^ 2 +
            (245760 : K[X]) * p.coeff 1 ^ 2 * g ^ 2 * f +
            (655360 : K[X]) * p.coeff 1 ^ 3 * g =
          H * ((((61440 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (192 : K[X])) * g ^ 2 -
                (61440 : K[X]) * p.coeff 1 ^ 2) * f ^ 2 +
            ((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * g * p.coeff 1 * f +
            ((3932160 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 ^ 2 +
            H * (((10240 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (32 : K[X])) * f ^ 3 +
              (Polynomial.C κ₃ * ((6144 : K[X]) * p.coeff 0) +
                Polynomial.C κ₇ * (4 : K[X]) -
                (983040 : K[X]) * p.coeff 0 ^ 2) * f +
              Polynomial.C κ * ((524288 : K[X]) * p.coeff 0 ^ 2) -
              Polynomial.C κ₅ * ((2048 : K[X]) * p.coeff 0) -
              Polynomial.C κ₉ - (4194304 : K[X]) * q.coeff 0))) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₂, hD0⟩ :=
    ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq ha
  have hkill : ∀ a : K, H.eval a = 0 → (p.coeff 3).eval a = 0 :=
    fun a ha => alignedThird_rootKill_p3_410 hrel ha
  obtain ⟨g, hg⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₄, hM60⟩ :=
    fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
  obtain ⟨f, hf, _hq4⟩ :=
    alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₆, hM100⟩ :=
    twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₈, hM14rel⟩ :=
    alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₈, hM140⟩ :=
    twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM14rel
  obtain ⟨κ₉, hM16⟩ :=
    alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore10 :=
    alignedNonsquareTenth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
      hM12form hM140 hM16
  have hq0 := alignedNonsquareTenth_solved_410 hH hcore10 hf
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, hD0, hM4, hM60, hM8form, hM100,
    hM12form, hM140, hM16, hf, hq0⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`3`
aligned row: BOTH chambers carry the chamber-free form `M₁₆ = κ₉ H¹⁵`;
the square chamber adds the NEW μ-loaded septic divisibility carrying
`s₁₀` on the fifth face's divisibility, the nonsquare chamber adds the
fifth face's divisibility.  Neither chamber is excluded and no closure
is claimed. -/
theorem normalized410ScaleTwo_alignedTenthRow_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₉ : K) (u v s₁₀ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2)
              (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 15 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (16 : K[X]) * ((143 : K[X]) * u ^ 4 -
                (264 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((663 : K[X]) * u ^ 7 -
                  (6552 : K[X]) * p.coeff 2 * u ^ 5 +
                  (20160 : K[X]) * p.coeff 2 ^ 2 * u ^ 3 -
                  (17920 : K[X]) * p.coeff 2 ^ 3 * u) = h0 * s₁₀) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₉ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2)
              (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 15 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, u, v, s₁₀, s₁₁, s₁₂, s₁₃,
      s₁₄, s₁₅, s₁₆, hp3, hM2f, _hM4, _hM6f, _hM8, _hM10f, _hM12f,
      _hM14f, hM16f, hv, hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7,
      _hq0⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₉, u, v, s₁₀, hp3, hM2f, hM16f,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedTenthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, _hM20, _hM4, _hM60, _hM8,
      _hM100, _hM12f, _hM140, hM16f, hf, _hq0⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₉, g, f, hg, hM16f, hf⟩

/-- Extended root data of the consumed degree-`3` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order — the deeper kills are in the previous root
packets), and the NEW degree-`3` content splits by chamber.  The square
chamber gains the NEW value tie `1280 u(a)⁴ v(a)³ = 5 μ u(a)⁷`, whose
clash with the sixth face's product kill
`u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a factor-`555` mismatch) RE-DERIVES
the root dichotomy `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`, plus
`s₁₀(a) = 0`, the `s₁₀`/`s₁₁` ties, the FIRST μ₄-loaded root tie on
`s₁₅`, and the `q₀` value tie — the first aligned root tie seeing
`κ₉`.  The nonsquare chamber's octic block dies at `a` and collapses
on the quadratic kill to the perfect-cube product
`g(a) (g(a) f(a) + 8 p₁(a))³ = 0` — an independent re-derivation of
the eighth face's pin content as a product kill; no new pin is claimed.
`q₀` does NOT vanish and no new vanishing is claimed; both dichotomy
branches are preserved. -/
theorem normalized410ScaleTwo_alignedTenthRow_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a : K) (κ : K), H.eval a = 0 ∧
      (8 : K[X]) * q.coeff 8 =
        H * ((15 : K[X]) * p.coeff 3 ^ 2 +
          (20 : K[X]) * p.coeff 2 * H ^ 2 + Polynomial.C κ * H ^ 3) ∧
      (p.coeff 3).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 ∧
      ((∃ (μ μ₂ μ₃ μ₄ κ₃ κ₅ κ₇ κ₉ : K)
          (h0 u v s₁₀ s₁₁ s₁₅ s₁₆ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (16 : K[X]) * ((143 : K[X]) * u ^ 4 -
                (264 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((663 : K[X]) * u ^ 7 -
                  (6552 : K[X]) * p.coeff 2 * u ^ 5 +
                  (20160 : K[X]) * p.coeff 2 ^ 2 * u ^ 3 -
                  (17920 : K[X]) * p.coeff 2 ^ 3 * u) = h0 * s₁₀ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (1280 : K) * u.eval a ^ 4 * v.eval a ^ 3 =
            (5 : K) * μ * u.eval a ^ 7 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₁₀.eval a =
            -(30720 : K) * (p.coeff 1).eval a * u.eval a ^ 3 *
              v.eval a ^ 2 ∧
          s₁₀.eval a = 0 ∧
          s₁₁.eval a =
            -(245760 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 2 *
                v.eval a -
              (672 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 4 -
              (3 : K) * μ₂ * u.eval a ^ 5 ∧
          s₁₅.eval a =
            ((6144 : K) * κ₃ * (p.coeff 0).eval a + (4 : K) * κ₇ -
                (983040 : K) * (p.coeff 0).eval a ^ 2) * v.eval a -
              (344064 : K) * μ * (p.coeff 0).eval a *
                (p.coeff 1).eval a -
              (2560 : K) * μ₂ * (p.coeff 0).eval a * u.eval a -
              (96 : K) * μ₃ * (p.coeff 1).eval a - μ₄ * u.eval a ∧
          (4194304 : K) * (q.coeff 0).eval a =
            (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
              (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
              s₁₆.eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (16 : K) * ((143 : K) * g.eval a ^ 4 -
                  (264 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
                  (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
                (15360 : K) * (p.coeff 1).eval a * g.eval a *
                  ((3 : K) * g.eval a ^ 2 -
                    (4 : K) * (p.coeff 2).eval a) * f.eval a ^ 2 +
                (245760 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 2 *
                  f.eval a +
                (655360 : K) * (p.coeff 1).eval a ^ 3 * g.eval a = 0 ∧
            g.eval a * (g.eval a * f.eval a +
                (8 : K) * (p.coeff 1).eval a) ^ 3 = 0)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  rcases hsource with
    ⟨hH, _hHdeg2, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hclear := alignedSecondDefect_clearing_410 hM
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    obtain ⟨μ, _hμ2, hDform⟩ :=
      ninthPower_squareChamber_form_410 hH hHsq hrel
    have hdeg1 : h0.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hHsq
      rw [hHdegree, Polynomial.natDegree_pow] at hdegree
      omega
    have hkill0 : ∀ b : K, h0.eval b = 0 → (p.coeff 3).eval b = 0 := by
      intro b hb
      apply alignedThird_rootKill_p3_410 hrel
      rw [hHsq]
      simp only [Polynomial.eval_pow, hb]
      norm_num
    obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
    obtain ⟨u, hu, _hq6⟩ :=
      alignedSquareFourth_descent_410 hh0 hdeg1 hcore
    have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
      fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
    obtain ⟨v, hv, _hq4⟩ :=
      alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
      twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
    have hcore7 :=
      alignedSquareSeventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form
    obtain ⟨s, hs, _hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₈, hM14rel⟩ :=
      alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₄, _hμ₄2, hM14form⟩ :=
      twentySeventhPower_squareChamber_form_410 hh0 hHsq hM14rel
    obtain ⟨κ₉, hM16⟩ :=
      alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore10 :=
      alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form hM16
    obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, hd1, hd2, hd3, hd4, hd5,
      hd6, hd7, hq0⟩ := alignedSquareTenth_solved_410 hh0 hcore10 hv
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hHroot : H.eval a = 0 := by
      rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hHroot
    have hp3d : (p.coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hkilla : u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hv
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hμtie : (80 : K) * u.eval a * v.eval a ^ 3 =
        μ * ((35 : K) * u.eval a ^ 4 -
          (336 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
          (1344 : K) * (p.coeff 2).eval a ^ 2) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hs
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hkilltie : u.eval a *
        ((16 : K) * v.eval a ^ 3 - (7 : K) * μ * u.eval a ^ 3) = 0 := by
      linear_combination (1 / 5 : K) * hμtie -
        (336 / 5 : K) * μ * (p.coeff 2).eval a * hkilla
    have hd1a :
        (16 : K) * ((143 : K) * u.eval a ^ 4 -
              (264 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
              (48 : K) * (p.coeff 2).eval a ^ 2) * v.eval a ^ 3 -
          μ * ((663 : K) * u.eval a ^ 7 -
            (6552 : K) * (p.coeff 2).eval a * u.eval a ^ 5 +
            (20160 : K) * (p.coeff 2).eval a ^ 2 * u.eval a ^ 3 -
            (17920 : K) * (p.coeff 2).eval a ^ 3 * u.eval a) = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd1
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hnewtie : (1280 : K) * u.eval a ^ 4 * v.eval a ^ 3 =
        (5 : K) * μ * u.eval a ^ 7 := by
      linear_combination hd1a +
        ((4480 : K) * μ * (p.coeff 2).eval a ^ 2 * u.eval a -
          (3920 : K) * μ * (p.coeff 2).eval a * u.eval a ^ 3 +
          (658 : K) * μ * u.eval a ^ 5 +
          (192 : K) * (p.coeff 2).eval a * v.eval a ^ 3 -
          (1008 : K) * u.eval a ^ 2 * v.eval a ^ 3) * hkilla
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h555 : ((555 : K) * μ) * u.eval a ^ 7 = 0 := by
          linear_combination hnewtie - (80 : K) * u.eval a ^ 4 * h16
        have h555μ : (555 : K) * μ = 0 :=
          (mul_eq_zero.mp h555).resolve_right (pow_ne_zero 7 hu)
        have hμ0 : μ = 0 :=
          (mul_eq_zero.mp h555μ).resolve_left (by norm_num)
        have h16v : (16 : K) * v.eval a ^ 3 = 0 := by
          rw [hμ0] at h16
          linear_combination h16
        have hv3 : v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp h16v).resolve_left (by norm_num)
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        exact Or.inr ⟨hv0, hμ0⟩
    have hs10raw : s₁₀.eval a =
        -(30720 : K) * (p.coeff 1).eval a * u.eval a ^ 3 *
          v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (15360 : K) * (p.coeff 1).eval a * u.eval a * v.eval a ^ 2 *
          hkilla
    have hs10kill : s₁₀.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs10raw, hu0]; ring
      · rw [hs10raw, hv0]; ring
    have hs11tie : s₁₁.eval a =
        -(245760 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 2 *
            v.eval a -
          (672 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 4 -
          (3 : K) * μ₂ * u.eval a ^ 5 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        ((10752 : K) * μ * (p.coeff 1).eval a * (p.coeff 2).eval a -
          (10752 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 2 +
          (240 : K) * μ₂ * (p.coeff 2).eval a * u.eval a -
          (80 : K) * μ₂ * u.eval a ^ 3) * hkilla
    have hs15tie : s₁₅.eval a =
        ((6144 : K) * κ₃ * (p.coeff 0).eval a + (4 : K) * κ₇ -
            (983040 : K) * (p.coeff 0).eval a ^ 2) * v.eval a -
          (344064 : K) * μ * (p.coeff 0).eval a * (p.coeff 1).eval a -
          (2560 : K) * μ₂ * (p.coeff 0).eval a * u.eval a -
          (96 : K) * μ₃ * (p.coeff 1).eval a - μ₄ * u.eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd7
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hq0tie : (4194304 : K) * (q.coeff 0).eval a =
        (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
          (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
          s₁₆.eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq0
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      linear_combination hev
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, μ₃, μ₄, κ₃, κ₅, κ₇, κ₉, h0, u, v, s₁₀, s₁₁, s₁₅,
        s₁₆, hh0, hHsq, hroot, hp3, hv, hd1, hp3d, hkilla, hnewtie,
        hdich, hs10raw, hs10kill, hs11tie, hs15tie, hq0tie⟩⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    obtain ⟨_hκ₂, hD0⟩ :=
      ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
    have hsimple : ∀ b : K, H.eval b = 0 → H.derivative.eval b ≠ 0 :=
      fun b hb =>
        nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq hb
    have hkill : ∀ b : K, H.eval b = 0 → (p.coeff 3).eval b = 0 :=
      fun b hb => alignedThird_rootKill_p3_410 hrel hb
    obtain ⟨g, hg⟩ :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₄, hM60⟩ :=
      fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
    obtain ⟨f, hf, _hq4⟩ :=
      alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₆, hM100⟩ :=
      twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₈, hM14rel⟩ :=
      alignedNinthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₈, hM140⟩ :=
      twentySeventhPower_nonsquareChamber_kill_410 hH hHdegree hnsq
        hM14rel
    obtain ⟨κ₉, hM16⟩ :=
      alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore10 :=
      alignedNonsquareTenth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
        hM12form hM140 hM16
    have hq0 := alignedNonsquareTenth_solved_410 hH hcore10 hf
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hg, Polynomial.eval_mul, hroot, zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hroot
    have hkilla : g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hf
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hbtie : (16 : K) * ((143 : K) * g.eval a ^ 4 -
            (264 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
            (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
        (15360 : K) * (p.coeff 1).eval a * g.eval a *
          ((3 : K) * g.eval a ^ 2 - (4 : K) * (p.coeff 2).eval a) *
          f.eval a ^ 2 +
        (245760 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 2 *
          f.eval a +
        (655360 : K) * (p.coeff 1).eval a ^ 3 * g.eval a = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq0
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hcube : (1280 : K) * (g.eval a *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3) =
        0 := by
      linear_combination hbtie +
        ((192 : K) * (p.coeff 2).eval a * f.eval a ^ 3 -
          (1008 : K) * g.eval a ^ 2 * f.eval a ^ 3 -
          (15360 : K) * (p.coeff 1).eval a * g.eval a *
            f.eval a ^ 2) * hkilla
    have hprod : g.eval a * (g.eval a * f.eval a +
        (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp hcube).resolve_left (by norm_num)
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hprod⟩⟩

#print axioms alignedTenthCoefficientJacobianRow_410
#print axioms alignedTenthDefect_weightedDerivative_identity_410
#print axioms alignedTenthDefectRow_eq_zero_410
#print axioms fifteenthPowerRelation_of_weightFifteenRow_410
#print axioms alignedTenthDefectPowerRelation_410
#print axioms alignedSquareTenth_core_410
#print axioms alignedSquareTenth_solved_410
#print axioms alignedNonsquareTenth_core_410
#print axioms alignedNonsquareTenth_solved_410
#print axioms normalized410ScaleTwo_alignedTenthRow_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedTenthRow_rootData

end Max11DegreeRoutes
