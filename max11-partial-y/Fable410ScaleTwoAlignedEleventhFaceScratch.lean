import Fable410ScaleTwoAlignedTenthFaceScratch

/-! # Eleventh aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedTenthFaceScratch` consumed the degree-`2`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`33/2` first integral `M₁₈² = κ₁₀ H³³`, the eight-deep square
peel carrying `s₁₇` through `s₂₄`, and the constant pin
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`.  This file consumes the
next unused aligned row, the degree-`1` Jacobian coefficient
`p₁' q₁ + 2 p₀' q₂ - (2 p₂ q₀' + p₁ q₁')` — the LAST aligned row above
the terminal degree-`0` Keller-constant row, and the second in a row
with no new letter: `q₀` enters through `q₀'` only (cofactor `2 p₂`),
`q₁` through its value and derivative, and `q₂` through `2 p₀' q₂`,
and every one of these letters was already consumed by a previous face
(internal names `alignedTwelfth*`).

At the common source level, modulo the face `N = 0` and the consumed
degree-`11` through degree-`2` brackets of `M₂` through `M₁₈`, the
degree-`1` row is the weighted derivative of the cleared twelfth
defect `M₂₀` (weight `18`, co-degree `12`), kept in factored form
through the previous defects: the head is the first weighted
p₀-CUBIC block `838860800 p₀³ H¹⁸ - 629145600 (p₀² p₁ p₃ + p₀² p₂²
+ 2 p₀ p₁² p₂) H¹⁶ - 104857600 p₁⁴ H¹⁶ + ...` with NO `q`-letter and
NO `κ`-module at all (the SECOND pure-`p` head), and neither `M₈` nor
`M₁₆` nor `M₁₈` appears among the corrections — the `q`-content flows
through `M₂`, `M₄`, `M₆`, `M₁₀`, `M₁₂`, `M₁₄` alone (`q₀` and `q₄`
drop out of the defect entirely).  The exact multiplier identity is

`671088640 H¹⁸ · row₁ = (H M₂₀' - 18 M₂₀ H')
  + 5 p₃ (2 H M₁₈' - 33 M₁₈ H') + 320 p₂ H² (H M₁₆' - 15 M₁₆ H')
  + (640 p₁ H⁴ + 160 p₂ p₃ H² - 20 p₃³) (2 H M₁₄' - 27 M₁₄ H')
  + (10240 p₀ H⁶ + 5120 p₁ p₃ H⁴ + 2560 p₂² H⁴ - 1280 p₂ p₃² H²
    + 160 p₃⁴) (H M₁₂' - 12 M₁₂ H')
  + (15360 p₀ p₃ H⁶ + 15360 p₁ p₂ H⁶ - 1920 p₁ p₃² H⁴
    - 1920 p₂² p₃ H⁴ + 800 p₂ p₃³ H² - 90 p₃⁵) (2 H M₁₀' - 21 M₁₀ H')
  + (655360 p₀ p₂ H⁸ + 327680 p₁² H⁸) (H M₈' - 9 M₈ H')
  + c₆ (2 H M₆' - 15 M₆ H') + c₄ (H M₄' - 6 M₄ H')
  + c₂ (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁷·5·H¹⁸` — the first aligned multiplier that is
not a pure power of two — and an EMPTY correction module for the
SIXTH row in a row; the row's entire `q₀'`-content is carried by the
`M₁₆` bracket with cofactor `320 p₂ H²`.  On the aligned face every
previous bracket vanishes, so `H M₂₀' = 18 M₂₀ H'` and the
weight-`18` first integral

`M₂₀ = κ₁₁ H¹⁸`

holds for a preserved constant `κ₁₁` — even-type and CHAMBER-FREE,
the SIXTH rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵, H¹⁸`; no
parity kill, `κ₁₁` is preserved in BOTH chambers.  The chamber core,
after cancelling `h₀²⁴` resp. `H¹²`, is a SEXTIC-cofactor cube plus a
`p₁`-loaded quintic square block:

`3200 (143 w⁶ - 572 p₂ w⁴ + 528 p₂² w² - 64 p₂³) (w² - 4 p₂)³
  + 51200 h p₁ w (187 w⁴ - 664 p₂ w² + 432 p₂²) (w² - 4 p₂)²`
  (`h = h₀²` resp. `H`)

and — because every `q`-letter of the row was already solved — the
whole relation is `q`-FREE in both chambers, and `κ`, `κ₅`, `κ₉` drop
out entirely.  The `μ`-block of the quotient factors through
`(u² - 4 p₂)` for the first time, so the leading peel is μ-FREE.

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`, `M₁₄ = μ₄ h₀²⁷`,
  `M₂₀ = κ₁₁ H¹⁸`: on the consumed divisibility `u² - 4 p₂ = h₀ v`
  the peel is NINE deep — the deepest aligned peel: the NEW μ-FREE
  leading divisibility

  `3200 (143 u⁶ - 572 p₂ u⁴ + 528 p₂² u² - 64 p₂³) v³ = h₀ s₂₅`

  — the first aligned peel whose head carries no constant at all —
  then the explicit peels producing `s₂₆` through `s₃₃` (`s₃₁` is
  loaded with `μ₄`), and the SECOND aligned CONSTANT PIN, now a
  `p₀`-CUBIC:

  `C κ₁₁ = 838860800 p₀³ - 7864320 κ₃ p₀² - 10240 κ₇ p₀ - s₃₃`

  — the row pins the even constant `κ₁₁` globally against the peel
  letters.  Combining the pin with the ninth face's solved row
  `4194304 q₀ = 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - s₁₆` eliminates the
  `p₀`-cubic and yields the GLOBAL `q₀`-backwire cross-tie

  `C κ C κ₁₁ = 6710886400 p₀ q₀ + 3276800 κ₅ p₀² + 1600 κ₉ p₀
    + 1600 p₀ s₁₆ - 7864320 κ κ₃ p₀² - 10240 κ κ₇ p₀ - κ s₃₃`

  — the FIRST global cross-face link between two aligned pins.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = M₁₈ = 0`, `M₄ = κ₃ H⁶`,
  `M₁₂ = κ₇ H¹²`, `M₂₀ = κ₁₁ H¹⁸`: on the consumed divisibility
  `g² - 4 p₂ = H f` the row yields the `q`-free block identity whose
  `H²`-part carries `κ₁₁ + 7864320 κ₃ p₀² + 10240 κ₇ p₀
  - 838860800 p₀³` — `κ₁₁` is TIED two `H`-levels deep (like the
  ninth face's `q₀`), not solved, and no parity kill occurs.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie as a PURE PRODUCT KILL `u(a)⁶ v(a)³ = 0` (the sextic
cofactor evaluates to `32 u⁶` on the kill and the μ-block dies), so
the root dichotomy `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)` is
derived DIRECTLY — `u = 0` or `v = 0` splits against the sixth face's
product kill `u (16 v³ - 7 μ u³) = 0` — plus `s₂₅(a) = 0` AND
`s₂₆(a) = 0` unconditionally (the first aligned double peel kill),
the μ₄-loaded tie `s₃₂(a) = -1638400 μ₂ p₀ p₁ - 640 μ₄ p₁`, the
`κ₁₁` value tie, and — combining with the eighth face's `q₁`-solve to
eliminate `κ₇` — the `q₁`-backwire root tie

`u κ₁₁ = 2684354560 p₀ q₁ - 1677721600 p₀³ u + 7864320 κ₃ p₀² u
  + 1310720 κ₅ p₀ p₁ - 671088640 κ p₀² p₁ - 2560 p₀ s₉ - s₃₃ u` at `a`.

The nonsquare chamber's block dies at `a` and collapses on the
quadratic kill to the PERFECT-CUBE PRODUCT

`g(a)³ · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content
with a `g³`-cofactor (no new pin is claimed).

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches are not excluded, and the
constants are preserved where not previously forced (`κ₁₁` is pinned
globally in the square chamber against the peel letters and tied two
`H`-levels deep in the nonsquare chamber, but not cleared).  The
aligned Jacobian tower now has ONLY the terminal degree-`0` row
`p₀' q₁ - p₁ q₀' = C j` — the inhomogeneous Keller-constant row —
left unused.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`1` Keller coefficient on the aligned face -/

/-- The twelfth row below the leading weighted-Wronskian row for
outer degrees `(4,10)`: the degree-`1` Jacobian coefficient, the last
aligned row above the terminal degree-`0` Keller-constant row.  It is
derived directly from the Keller bracket. -/
theorem alignedTwelfthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 1).derivative * q.coeff 1 +
        (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
      ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
        p.coeff 1 * (q.coeff 1).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 1) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (1 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC2]
  linear_combination hcoeff

/-! ## Aligned twelfth defect -/

set_option maxHeartbeats 800000 in
/-- Cleared twelfth defect of the degree-`1` aligned `(4,10)` row,
kept in factored form through the third through ninth defects.  Every
monomial has exact `H`-weight `18`.  The head is the first weighted
`p₀`-CUBIC block, PURE in the `p`-letters: no `q`-letter and no
`κ`-module at all, and neither `M₈` nor `M₁₆` nor `M₁₈` appears among
the corrections — `q₀` and `q₄` drop out of the defect entirely. -/
def alignedTwelfthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (838860800 : K[X]) * H ^ 18 * a0 ^ 3 -
    (104857600 : K[X]) * H ^ 16 * a1 ^ 4 -
    (1258291200 : K[X]) * H ^ 16 * a0 * a1 ^ 2 * a2 -
    (629145600 : K[X]) * H ^ 16 * a0 ^ 2 * a2 ^ 2 -
    (629145600 : K[X]) * H ^ 16 * a0 ^ 2 * a1 * a3 +
    (314572800 : K[X]) * H ^ 14 * a1 ^ 2 * a2 ^ 3 +
    (524288000 : K[X]) * H ^ 14 * a1 ^ 3 * a2 * a3 +
    (157286400 : K[X]) * H ^ 14 * a0 * a2 ^ 4 +
    (1572864000 : K[X]) * H ^ 14 * a0 * a1 * a2 ^ 2 * a3 +
    (629145600 : K[X]) * H ^ 14 * a0 * a1 ^ 2 * a3 ^ 2 +
    (629145600 : K[X]) * H ^ 14 * a0 ^ 2 * a2 * a3 ^ 2 -
    (13107200 : K[X]) * H ^ 12 * a2 ^ 6 -
    (353894400 : K[X]) * H ^ 12 * a1 * a2 ^ 4 * a3 -
    (943718400 : K[X]) * H ^ 12 * a1 ^ 2 * a2 ^ 2 * a3 ^ 2 -
    (183500800 : K[X]) * H ^ 12 * a1 ^ 3 * a3 ^ 3 -
    (629145600 : K[X]) * H ^ 12 * a0 * a2 ^ 3 * a3 ^ 2 -
    (1101004800 : K[X]) * H ^ 12 * a0 * a1 * a2 * a3 ^ 3 -
    (117964800 : K[X]) * H ^ 12 * a0 ^ 2 * a3 ^ 4 +
    (117964800 : K[X]) * H ^ 10 * a2 ^ 5 * a3 ^ 2 +
    (720896000 : K[X]) * H ^ 10 * a1 * a2 ^ 3 * a3 ^ 3 +
    (491520000 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 ^ 4 +
    (491520000 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 ^ 4 +
    (176947200 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 5 -
    (200704000 : K[X]) * H ^ 8 * a2 ^ 4 * a3 ^ 4 -
    (447283200 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 5 -
    (68812800 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 6 -
    (137625600 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 6 +
    (137625600 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 6 +
    (110592000 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 7 +
    (12902400 : K[X]) * H ^ 6 * a0 * a3 ^ 8 -
    (45619200 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 8 -
    (9574400 : K[X]) * H ^ 4 * a1 * a3 ^ 9 +
    (7321600 : K[X]) * H ^ 2 * a2 * a3 ^ 10 -
    (457600 : K[X]) * a3 ^ 12 -
    ((640 : K[X]) * H ^ 4 * a1 -
      (320 : K[X]) * H ^ 2 * a2 * a3 +
      (80 : K[X]) * a3 ^ 3) *
      alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((10240 : K[X]) * H ^ 6 * a0 -
      (2560 : K[X]) * H ^ 4 * a2 ^ 2 -
      (2560 : K[X]) * H ^ 4 * a1 * a3 +
      (2560 : K[X]) * H ^ 2 * a2 * a3 ^ 2 -
      (480 : K[X]) * a3 ^ 4) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    (-(15360 : K[X]) * H ^ 6 * a1 * a2 +
      (7680 : K[X]) * H ^ 4 * a2 ^ 2 * a3 +
      (5760 : K[X]) * H ^ 4 * a1 * a3 ^ 2 -
      (4800 : K[X]) * H ^ 2 * a2 * a3 ^ 3 +
      (720 : K[X]) * a3 ^ 5) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    ((1638400 : K[X]) * H ^ 10 * a0 * a1 -
      (614400 : K[X]) * H ^ 8 * a1 * a2 ^ 2 -
      (409600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 -
      (819200 : K[X]) * H ^ 8 * a0 * a2 * a3 +
      (307200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 +
      (768000 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 +
      (204800 : K[X]) * H ^ 6 * a0 * a3 ^ 3 -
      (358400 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 -
      (156800 : K[X]) * H ^ 4 * a1 * a3 ^ 4 +
      (123200 : K[X]) * H ^ 2 * a2 * a3 ^ 5 -
      (13200 : K[X]) * a3 ^ 7) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((7864320 : K[X]) * H ^ 12 * a0 ^ 2 -
      (3932160 : K[X]) * H ^ 10 * a1 ^ 2 * a2 -
      (3932160 : K[X]) * H ^ 10 * a0 * a2 ^ 2 -
      (3932160 : K[X]) * H ^ 10 * a0 * a1 * a3 +
      (491520 : K[X]) * H ^ 8 * a2 ^ 4 +
      (4915200 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 +
      (1966080 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 +
      (3932160 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 -
      (1966080 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 -
      (3440640 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 -
      (737280 : K[X]) * H ^ 6 * a0 * a3 ^ 4 +
      (1536000 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 +
      (552960 : K[X]) * H ^ 4 * a1 * a3 ^ 5 -
      (430080 : K[X]) * H ^ 2 * a2 * a3 ^ 6 +
      (40320 : K[X]) * a3 ^ 8) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    (-(9175040 : K[X]) * H ^ 12 * a1 ^ 3 -
      (55050240 : K[X]) * H ^ 12 * a0 * a1 * a2 +
      (11468800 : K[X]) * H ^ 10 * a1 * a2 ^ 3 +
      (27525120 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 +
      (27525120 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 +
      (20643840 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 2 -
      (5734400 : K[X]) * H ^ 8 * a2 ^ 4 * a3 -
      (30105600 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 2 -
      (8601600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 3 -
      (17203200 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 3 +
      (10752000 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 3 +
      (14515200 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 4 +
      (2580480 : K[X]) * H ^ 6 * a0 * a3 ^ 5 -
      (6289920 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 5 -
      (1921920 : K[X]) * H ^ 4 * a1 * a3 ^ 6 +
      (1485120 : K[X]) * H ^ 2 * a2 * a3 ^ 7 -
      (123760 : K[X]) * a3 ^ 9) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
/-- Exact combination of the degree-`1` Jacobian expression with the
weight-`18` bracket of `M₂₀`.  The corrections are the consumed
degree-`10` through degree-`2` brackets of `M₂` through `M₁₈`: neither
the aligned-face residual `N` nor the degree-`11` relation `R`
appears — the correction module is empty for the sixth row in a row —
and the `M₁₆` bracket carries the row's entire `q₀'`-content with
cofactor `320 p₂ H²`.  Every correction vanishes on the aligned
face. -/
theorem alignedTwelfthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (671088640 : K[X]) * H ^ 18 *
        (a1.derivative * b1 +
          a0.derivative * (b2 * (2 : K[X])) -
        ((a2 * (2 : K[X])) * b0.derivative +
          a1 * b1.derivative)) =
      (H * (alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
          κ).derivative -
        (18 : K[X]) *
          alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        ((5 : K[X]) * a3) *
          ((2 : K[X]) * H *
              (alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (33 : K[X]) *
              alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((320 : K[X]) * H ^ 2 * a2) *
          (H * (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6
              b7 κ).derivative -
            (15 : K[X]) *
              alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
                κ * H.derivative) +
        ((640 : K[X]) * H ^ 4 * a1 +
            (160 : K[X]) * H ^ 2 * a2 * a3 -
            (20 : K[X]) * a3 ^ 3) *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((10240 : K[X]) * H ^ 6 * a0 +
            (2560 : K[X]) * H ^ 4 * a2 ^ 2 +
            (5120 : K[X]) * H ^ 4 * a1 * a3 -
            (1280 : K[X]) * H ^ 2 * a2 * a3 ^ 2 +
            (160 : K[X]) * a3 ^ 4) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((15360 : K[X]) * H ^ 6 * a1 * a2 +
            (15360 : K[X]) * H ^ 6 * a0 * a3 -
            (1920 : K[X]) * H ^ 4 * a2 ^ 2 * a3 -
            (1920 : K[X]) * H ^ 4 * a1 * a3 ^ 2 +
            (800 : K[X]) * H ^ 2 * a2 * a3 ^ 3 -
            (90 : K[X]) * a3 ^ 5) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((327680 : K[X]) * H ^ 8 * a1 ^ 2 +
            (655360 : K[X]) * H ^ 8 * a0 * a2) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6
              b7 κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((1638400 : K[X]) * H ^ 10 * a0 * a1 +
            (204800 : K[X]) * H ^ 8 * a1 * a2 ^ 2 +
            (204800 : K[X]) * H ^ 8 * a1 ^ 2 * a3 +
            (409600 : K[X]) * H ^ 8 * a0 * a2 * a3 -
            (51200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 -
            (153600 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 -
            (51200 : K[X]) * H ^ 6 * a0 * a3 ^ 3 +
            (44800 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 +
            (22400 : K[X]) * H ^ 4 * a1 * a3 ^ 4 -
            (12320 : K[X]) * H ^ 2 * a2 * a3 ^ 5 +
            (1100 : K[X]) * a3 ^ 7) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((7864320 : K[X]) * H ^ 12 * a0 ^ 2 +
            (3932160 : K[X]) * H ^ 10 * a1 ^ 2 * a2 +
            (3932160 : K[X]) * H ^ 10 * a0 * a2 ^ 2 +
            (7864320 : K[X]) * H ^ 10 * a0 * a1 * a3 -
            (163840 : K[X]) * H ^ 8 * a2 ^ 4 -
            (1966080 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 -
            (983040 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 -
            (1966080 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 +
            (491520 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 +
            (983040 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 +
            (245760 : K[X]) * H ^ 6 * a0 * a3 ^ 4 -
            (307200 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 -
            (122880 : K[X]) * H ^ 4 * a1 * a3 ^ 5 +
            (71680 : K[X]) * H ^ 2 * a2 * a3 ^ 6 -
            (5760 : K[X]) * a3 ^ 8) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((9175040 : K[X]) * H ^ 12 * a1 ^ 3 +
            (55050240 : K[X]) * H ^ 12 * a0 * a1 * a2 +
            (27525120 : K[X]) * H ^ 12 * a0 ^ 2 * a3 -
            (2293760 : K[X]) * H ^ 10 * a1 * a2 ^ 3 -
            (6881280 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 -
            (6881280 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 -
            (6881280 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 2 +
            (716800 : K[X]) * H ^ 8 * a2 ^ 4 * a3 +
            (4300800 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 2 +
            (1433600 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 3 +
            (2867200 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 3 -
            (1075200 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 3 -
            (1612800 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 4 -
            (322560 : K[X]) * H ^ 6 * a0 * a3 ^ 5 +
            (524160 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 5 +
            (174720 : K[X]) * H ^ 4 * a1 * a3 ^ 6 -
            (106080 : K[X]) * H ^ 2 * a2 * a3 ^ 7 +
            (7735 : K[X]) * a3 ^ 9) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [alignedTwelfthDefect410, alignedEleventhDefect410,
    alignedTenthDefect410, alignedNinthDefect410, alignedEighthDefect410,
    alignedSeventhDefect410, alignedSixthDefect410, alignedFifthDefect410,
    alignedFourthDefect410, alignedThirdDefect410,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_neg,
    Polynomial.derivative_ofNat, Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat, Polynomial.eval_zero]
  ring

/-- On the aligned face, with the consumed degree-`11` through
degree-`2` rows, the degree-`1` row is the weighted derivative
`H M₂₀' - 18 M₂₀ H' = 0`. -/
theorem alignedTwelfthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (18 : K[X]) *
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedTwelfthCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC2] at hrow
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
  have hB16 :=
    alignedTenthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB18 :=
    alignedEleventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedTwelfthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 0)
    (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12, hB14, hB16, hB18] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-`18` polynomial first integral -/

/-- Generic Wronskian quotient for the weight-`18` bracket: over a
characteristic-zero field, `H D' - 18 D H' = 0` forces
`D = C c * H¹⁸`.  Even-type: no squaring, no parity split. -/
theorem eighteenthPowerRelation_of_weightEighteenRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (18 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 18 := by
  have hC18 : Polynomial.C (18 : K) = (18 : K[X]) :=
    Polynomial.C_eq_natCast 18
  have hW : Polynomial.wronskian D (H ^ 18) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (18 : K) * H ^ (18 - 1) * H.derivative) -
          D.derivative * H ^ 18 =
          H ^ 17 *
            (Polynomial.C (18 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC18]
        have hfac :
            (18 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 18 hH) hW

/-- Weight-eighteen polynomial first integral of the aligned `(4,10)`
twelfth defect: `M₂₀ = κ₁₁ H¹⁸` — even-type and chamber-free, the
sixth rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵, H¹⁸`. -/
theorem alignedTwelfthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₁₁ : K,
      alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₁₁ * H ^ 18 :=
  eighteenthPowerRelation_of_weightEighteenRow_410 hH
    (alignedTwelfthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared square-core form of the twelfth defect relation:
cancelling `h₀²⁴` from `M₂₀ = κ₁₁ H¹⁸` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core carried by `h₀³` against
the explicit quotient; the μ-block factors through `(u² - 4 p₂)`, so
the level-zero quotient block is μ-loaded with no constant term.
Neither `M₈` nor `M₁₆` nor `M₁₈` enters, and the whole relation is
`q`-free and `κ`/`κ₅`/`κ₉`-free. -/
theorem alignedSquareTwelfth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ μ₃ κ₇ μ₄ κ₁₁ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₄ * h0 ^ 27)
    (hM20 : alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₁₁ * H ^ 18) :
    (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
          (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
      (51200 : K[X]) * h0 ^ 2 * a1 * u *
          ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
            (432 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
      ((Polynomial.C μ * ((123760 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 4) +
            Polynomial.C μ * ((495040 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2))) +
        h0 * ((12902400 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 4 -
            Polynomial.C κ₃ * ((40320 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 4) -
            (68812800 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (68812800 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 -
            Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) -
            (334233600 : K[X]) * a1 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
            (78643200 : K[X]) * a0 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
        h0 ^ 2 * (Polynomial.C μ₂ * ((13200 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ * ((1921920 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
            Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3)) +
        h0 ^ 3 * ((176947200 : K[X]) * a0 * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (183500800 : K[X]) * a1 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2) +
            (314572800 : K[X]) * a0 * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            (209715200 : K[X]) * a1 ^ 3 * a2 * u) +
        h0 ^ 4 * (-Polynomial.C μ₃ * ((720 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C μ₂ * ((156800 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ * ((2580480 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
            Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
            Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u)) +
        h0 ^ 5 * (-(117964800 : K[X]) * a0 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
            Polynomial.C κ₇ * ((480 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
            (629145600 : K[X]) * a0 * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
            (314572800 : K[X]) * a0 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) +
            Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
            (104857600 : K[X]) * a1 ^ 4 +
            (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
            Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
        h0 ^ 6 * (-Polynomial.C μ₄ * ((80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₃ * ((5760 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
            Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
            Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
            Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2)) +
        h0 ^ 7 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * u +
            Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
            Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u)) +
        h0 ^ 8 * (-Polynomial.C μ₄ * ((640 : K[X]) * a1) -
            Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1)) +
        h0 ^ 9 * ((838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))) := by
  have hM20' := hM20
  simp only [alignedTwelfthDefect410] at hM20'
  rw [hM14, hM12, hM10, hM6, hM4, hM2, hHsq, hp3] at hM20'
  apply mul_left_cancel₀ (pow_ne_zero 24 hh0)
  linear_combination -hM20'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`1` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains
`h₀³`, and the peel is NINE deep: the NEW μ-FREE leading divisibility
`3200 (143 u⁶ - 572 p₂ u⁴ + 528 p₂² u² - 64 p₂³) v³ = h₀ s₂₅`, the
explicit peels producing `s₂₆` through `s₃₃` (`s₃₁` is loaded with
`μ₄`), and — with no letter left to solve — the SECOND aligned
CONSTANT PIN, now a `p₀`-cubic:
`C κ₁₁ = 838860800 p₀³ - 7864320 κ₃ p₀² - 10240 κ₇ p₀ - s₃₃`. -/
theorem alignedSquareTwelfth_solved_410 {K : Type*} [Field K]
    [CharZero K] {h0 u v a0 a1 a2 : K[X]} {μ κ₃ μ₂ μ₃ κ₇ μ₄ κ₁₁ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
            (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (51200 : K[X]) * h0 ^ 2 * a1 * u *
            ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
              (432 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
        ((Polynomial.C μ * ((123760 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 4) +
              Polynomial.C μ * ((495040 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2))) +
          h0 * ((12902400 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 4 -
              Polynomial.C κ₃ * ((40320 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 4) -
              (68812800 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (68812800 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3 -
              Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) -
              (334233600 : K[X]) * a1 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (78643200 : K[X]) * a0 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 * (Polynomial.C μ₂ * ((13200 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ * ((1921920 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 3) +
              Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3)) +
          h0 ^ 3 * ((176947200 : K[X]) * a0 * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (183500800 : K[X]) * a1 ^ 3 * u * (u ^ 2 - (4 : K[X]) * a2) +
              (314572800 : K[X]) * a0 * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2) -
              Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              (209715200 : K[X]) * a1 ^ 3 * a2 * u) +
          h0 ^ 4 * (-Polynomial.C μ₃ * ((720 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C μ₂ * ((156800 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ * ((2580480 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2) -
              Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
              Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u)) +
          h0 ^ 5 * (-(117964800 : K[X]) * a0 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              Polynomial.C κ₇ * ((480 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (u ^ 2 - (4 : K[X]) * a2) ^ 2) +
              (629145600 : K[X]) * a0 * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
              (314572800 : K[X]) * a0 ^ 2 * a2 * (u ^ 2 - (4 : K[X]) * a2) +
              Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (u ^ 2 - (4 : K[X]) * a2)) -
              (104857600 : K[X]) * a1 ^ 4 +
              (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
              Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
          h0 ^ 6 * (-Polynomial.C μ₄ * ((80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₃ * ((5760 : K[X]) * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * (u ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
              Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
              Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
              Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2)) +
          h0 ^ 7 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * u +
              Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u)) +
          h0 ^ 8 * (-Polynomial.C μ₄ * ((640 : K[X]) * a1) -
              Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1)) +
          h0 ^ 9 * ((838860800 : K[X]) * a0 ^ 3 -
              Polynomial.C κ₁₁ * ((1 : K[X])) -
              Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₂₅ s₂₆ s₂₇ s₂₈ s₂₉ s₃₀ s₃₁ s₃₂ s₃₃ : K[X],
      (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * a2 * u ^ 4 +
          (528 : K[X]) * a2 ^ 2 * u ^ 2 - (64 : K[X]) * a2 ^ 3) * v ^ 3 =
      h0 * s₂₅ ∧
      s₂₅ + (51200 : K[X]) * a1 * u *
        ((187 : K[X]) * u ^ 4 - (664 : K[X]) * a2 * u ^ 2 +
          (432 : K[X]) * a2 ^ 2) * v ^ 2 +
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) = h0 * s₂₆ ∧
      s₂₆ +
        (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v -
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) +
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) = h0 * s₂₇ ∧
      s₂₇ +
        (334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 +
        (209715200 : K[X]) * a1 ^ 3 * a2 * u -
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 -
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) -
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) -
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) +
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) = h0 * s₂₈ ∧
      s₂₈ +
        (68812800 : K[X]) * a1 ^ 2 * v ^ 3 +
        (183500800 : K[X]) * a1 ^ 3 * u * v -
        (68812800 : K[X]) * a0 * a2 * v ^ 3 -
        (314572800 : K[X]) * a0 * a1 * a2 * u * v -
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) -
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) -
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) -
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) -
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) +
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) +
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) = h0 * s₂₉ ∧
      s₂₉ -
        (12902400 : K[X]) * a0 * v ^ 4 -
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 +
        (104857600 : K[X]) * a1 ^ 4 -
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 +
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) -
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) -
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) -
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) -
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) +
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) +
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) +
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) = h0 * s₃₀ ∧
      s₃₀ -
        (629145600 : K[X]) * a0 * a1 ^ 2 * v +
        (314572800 : K[X]) * a0 ^ 2 * a2 * v +
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) +
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) -
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) -
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) +
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) -
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) +
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) -
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) = h0 * s₃₁ ∧
      s₃₁ +
        (117964800 : K[X]) * a0 ^ 2 * v ^ 2 +
        (629145600 : K[X]) * a0 ^ 2 * a1 * u +
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) +
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) +
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) +
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) -
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) -
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) -
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) = h0 * s₃₂ ∧
      s₃₂ +
        Polynomial.C μ₄ * ((640 : K[X]) * a1) +
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) = h0 * s₃₃ ∧
      Polynomial.C κ₁₁ =
        (838860800 : K[X]) * a0 ^ 3 -
          Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
          Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) - s₃₃ := by
  obtain ⟨s₃₃, hs9⟩ : ∃ w : K[X],
      w = (838860800 : K[X]) * a0 ^ 3 -
        Polynomial.C κ₁₁ * ((1 : K[X])) -
        Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
        Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨s₃₂, hs8⟩ : ∃ w : K[X],
      w = -Polynomial.C μ₄ * ((640 : K[X]) * a1) -
        Polynomial.C μ₂ * ((1638400 : K[X]) * a0 * a1) + h0 * s₃₃ := ⟨_, rfl⟩
  obtain ⟨s₃₁, hs7⟩ : ∃ w : K[X],
      w = -(117964800 : K[X]) * a0 ^ 2 * v ^ 2 -
        (629145600 : K[X]) * a0 ^ 2 * a1 * u -
        Polynomial.C μ₄ * ((80 : K[X]) * u * v) -
        Polynomial.C μ₃ * ((5760 : K[X]) * a1 * v) -
        Polynomial.C μ₂ * ((204800 : K[X]) * a0 * u * v) -
        Polynomial.C μ * ((20643840 : K[X]) * a0 * a1 * v) +
        Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) +
        Polynomial.C κ₇ * ((2560 : K[X]) * a1 * u) +
        Polynomial.C κ₃ * ((737280 : K[X]) * a0 * v ^ 2) +
        Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * u) + h0 * s₃₂ := ⟨_, rfl⟩
  obtain ⟨s₃₀, hs6⟩ : ∃ w : K[X],
      w = (629145600 : K[X]) * a0 * a1 ^ 2 * v -
        (314572800 : K[X]) * a0 ^ 2 * a2 * v -
        Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) -
        Polynomial.C μ₃ * ((7680 : K[X]) * a1 * a2) +
        Polynomial.C μ₂ * ((156800 : K[X]) * a1 * v ^ 2) +
        Polynomial.C μ₂ * ((409600 : K[X]) * a1 ^ 2 * u) -
        Polynomial.C μ * ((2580480 : K[X]) * a0 * u * v ^ 2) +
        Polynomial.C μ * ((9175040 : K[X]) * a1 ^ 3) -
        Polynomial.C μ * ((27525120 : K[X]) * a0 * a1 * a2) +
        Polynomial.C κ₇ * ((1280 : K[X]) * a2 * v) -
        Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * v) +
        Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * v) + h0 * s₃₁ := ⟨_, rfl⟩
  obtain ⟨s₂₉, hs5⟩ : ∃ w : K[X],
      w = (12902400 : K[X]) * a0 * v ^ 4 +
        (176947200 : K[X]) * a0 * a1 * u * v ^ 2 -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C μ₃ * ((960 : K[X]) * a2 * u * v) +
        Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) +
        Polynomial.C μ₂ * ((486400 : K[X]) * a1 * a2 * v) +
        Polynomial.C μ * ((1921920 : K[X]) * a1 * v ^ 3) +
        Polynomial.C μ * ((8601600 : K[X]) * a1 ^ 2 * u * v) -
        Polynomial.C μ * ((3440640 : K[X]) * a0 * a2 * u * v) -
        Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) -
        Polynomial.C κ₃ * ((552960 : K[X]) * a1 * u * v ^ 2) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) + h0 * s₃₀ := ⟨_, rfl⟩
  obtain ⟨s₂₈, hs4⟩ : ∃ w : K[X],
      w = -(68812800 : K[X]) * a1 ^ 2 * v ^ 3 -
        (183500800 : K[X]) * a1 ^ 3 * u * v +
        (68812800 : K[X]) * a0 * a2 * v ^ 3 +
        (314572800 : K[X]) * a0 * a1 * a2 * u * v +
        Polynomial.C μ₂ * ((35200 : K[X]) * a2 * u * v ^ 2) +
        Polynomial.C μ₂ * ((51200 : K[X]) * a1 * a2 ^ 2) +
        Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) +
        Polynomial.C μ * ((8547840 : K[X]) * a1 * a2 * v ^ 2) +
        Polynomial.C μ * ((6881280 : K[X]) * a1 ^ 2 * a2 * u) -
        Polynomial.C κ₃ * ((215040 : K[X]) * a2 * v ^ 3) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * u * v) + h0 * s₂₉ := ⟨_, rfl⟩
  obtain ⟨s₂₇, hs3⟩ : ∃ w : K[X],
      w = -(334233600 : K[X]) * a1 ^ 2 * a2 * v ^ 2 -
        (209715200 : K[X]) * a1 ^ 3 * a2 * u +
        (78643200 : K[X]) * a0 * a2 ^ 2 * v ^ 2 +
        Polynomial.C μ₂ * ((6400 : K[X]) * a2 ^ 2 * u * v) +
        Polynomial.C μ * ((495040 : K[X]) * a2 * u * v ^ 3) +
        Polynomial.C μ * ((6236160 : K[X]) * a1 * a2 ^ 2 * v) -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * v ^ 2) + h0 * s₂₈ := ⟨_, rfl⟩
  obtain ⟨s₂₆, hs2⟩ : ∃ w : K[X],
      w = -(314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * v +
        Polynomial.C μ * ((349440 : K[X]) * a2 ^ 2 * u * v ^ 2) -
        Polynomial.C μ * ((286720 : K[X]) * a1 * a2 ^ 3) + h0 * s₂₇ := ⟨_, rfl⟩
  obtain ⟨s₂₅, hs1⟩ : ∃ w : K[X],
      w = -(9574400 : K[X]) * a1 * u ^ 5 * v ^ 2 +
        (33996800 : K[X]) * a1 * a2 * u ^ 3 * v ^ 2 -
        (22118400 : K[X]) * a1 * a2 ^ 2 * u * v ^ 2 -
        Polynomial.C μ * ((35840 : K[X]) * a2 ^ 3 * u * v) + h0 * s₂₆ := ⟨_, rfl⟩
  refine ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
    linear_combination hcore
  · rw [hs1]
    ring
  · rw [hs2]
    ring
  · rw [hs3]
    ring
  · rw [hs4]
    ring
  · rw [hs5]
    ring
  · rw [hs6]
    ring
  · rw [hs7]
    ring
  · rw [hs8]
    ring
  · rw [hs9]
    ring

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared nonsquare-core form of the twelfth defect relation:
cancelling `H¹²` from `M₂₀ = κ₁₁ H¹⁸` on `p₃ = H g`,
`M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₁₂ = κ₇ H¹²` exposes the
same core in `g` carried by `H²` against the explicit quotient — no
parity kill: `κ₁₁` survives the nonsquare chamber, tied in the
`H²`-part of the quotient. -/
theorem alignedNonsquareTwelfth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₇ κ₁₁ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM2z : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6z : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM10z : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM14z : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM20 : alignedTwelfthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₁₁ * H ^ 18) :
    (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
          (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
      (51200 : K[X]) * H * a1 * g *
          ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
            (432 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
      (((12902400 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 4 -
            Polynomial.C κ₃ * ((40320 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 4) -
            (68812800 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
            (68812800 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 -
            Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3) -
            (334233600 : K[X]) * a1 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
            (78643200 : K[X]) * a0 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
        H * ((176947200 : K[X]) * a0 * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
            (183500800 : K[X]) * a1 ^ 3 * g * (g ^ 2 - (4 : K[X]) * a2) +
            (314572800 : K[X]) * a0 * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2)) -
            (209715200 : K[X]) * a1 ^ 3 * a2 * g) +
        H ^ 2 * (-(117964800 : K[X]) * a0 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
            Polynomial.C κ₇ * ((480 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
            (629145600 : K[X]) * a0 * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
            (314572800 : K[X]) * a0 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) +
            Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
            Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
            Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
            (104857600 : K[X]) * a1 ^ 4 +
            (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
            Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
        H ^ 3 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * g +
            Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) +
            Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g)) +
        H ^ 4 * ((838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))) := by
  have hM20' := hM20
  simp only [alignedTwelfthDefect410] at hM20'
  rw [hM14z, hM12, hM10z, hM6z, hM4, hM2z, hg] at hM20'
  apply mul_left_cancel₀ (pow_ne_zero 12 hH)
  linear_combination -hM20'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`1` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` the row yields a `q`-free block
identity whose `H²`-part carries the tied constant block
`κ₁₁ + 7864320 κ₃ p₀² + 10240 κ₇ p₀ - 838860800 p₀³` — `κ₁₁` is tied
two `H`-levels deep, not solved.  The block collapses at the core
root to the perfect-cube product `102400 g³ (g f + 8 p₁)³`. -/
theorem alignedNonsquareTwelfth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 : K[X]} {κ₃ κ₇ κ₁₁ : K}
    (hH : H ≠ 0)
    (hcore :
      (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
            (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (51200 : K[X]) * H * a1 * g *
            ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
              (432 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
        (((12902400 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 4 -
              Polynomial.C κ₃ * ((40320 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 4) -
              (68812800 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (68812800 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3 -
              Polynomial.C κ₃ * ((215040 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 3) -
              (334233600 : K[X]) * a1 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (78643200 : K[X]) * a0 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
          H * ((176947200 : K[X]) * a0 * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
              Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2) -
              (183500800 : K[X]) * a1 ^ 3 * g * (g ^ 2 - (4 : K[X]) * a2) +
              (314572800 : K[X]) * a0 * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2) -
              Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * (g ^ 2 - (4 : K[X]) * a2)) -
              (209715200 : K[X]) * a1 ^ 3 * a2 * g) +
          H ^ 2 * (-(117964800 : K[X]) * a0 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              Polynomial.C κ₇ * ((480 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              Polynomial.C κ₃ * ((737280 : K[X]) * a0 * (g ^ 2 - (4 : K[X]) * a2) ^ 2) +
              (629145600 : K[X]) * a0 * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (314572800 : K[X]) * a0 ^ 2 * a2 * (g ^ 2 - (4 : K[X]) * a2) +
              Polynomial.C κ₇ * ((1280 : K[X]) * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2)) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * (g ^ 2 - (4 : K[X]) * a2)) -
              (104857600 : K[X]) * a1 ^ 4 +
              (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
              Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2)) +
          H ^ 3 * (-(629145600 : K[X]) * a0 ^ 2 * a1 * g +
              Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g)) +
          H ^ 4 * ((838860800 : K[X]) * a0 ^ 3 -
              Polynomial.C κ₁₁ * ((1 : K[X])) -
              Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
              Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2))))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * a2 * g ^ 4 +
          (528 : K[X]) * a2 ^ 2 * g ^ 2 - (64 : K[X]) * a2 ^ 3) * f ^ 3 +
      (51200 : K[X]) * a1 * g *
        ((187 : K[X]) * g ^ 4 - (664 : K[X]) * a2 * g ^ 2 +
          (432 : K[X]) * a2 ^ 2) * f ^ 2 +
      (314572800 : K[X]) * a1 ^ 2 * a2 ^ 2 * f +
      (209715200 : K[X]) * a1 ^ 3 * a2 * g =
      H * (-(334233600 : K[X]) * a1 ^ 2 * a2 * f ^ 2 -
        (183500800 : K[X]) * a1 ^ 3 * g * f +
        (78643200 : K[X]) * a0 * a2 ^ 2 * f ^ 2 +
        (314572800 : K[X]) * a0 * a1 * a2 * g * f -
        (104857600 : K[X]) * a1 ^ 4 +
        (1258291200 : K[X]) * a0 * a1 ^ 2 * a2 -
        Polynomial.C κ₃ * ((245760 : K[X]) * a2 ^ 2 * f ^ 2) -
        Polynomial.C κ₃ * ((983040 : K[X]) * a1 * a2 * g * f) -
        Polynomial.C κ₃ * ((3932160 : K[X]) * a1 ^ 2 * a2) +
      H * (-(68812800 : K[X]) * a1 ^ 2 * f ^ 3 +
          (68812800 : K[X]) * a0 * a2 * f ^ 3 +
          (176947200 : K[X]) * a0 * a1 * g * f ^ 2 +
          (629145600 : K[X]) * a0 * a1 ^ 2 * f -
          (314572800 : K[X]) * a0 ^ 2 * a2 * f -
          (629145600 : K[X]) * a0 ^ 2 * a1 * g +
          Polynomial.C κ₇ * ((1280 : K[X]) * a2 * f) +
          Polynomial.C κ₇ * ((2560 : K[X]) * a1 * g) -
          Polynomial.C κ₃ * ((215040 : K[X]) * a2 * f ^ 3) -
          Polynomial.C κ₃ * ((552960 : K[X]) * a1 * g * f ^ 2) -
          Polynomial.C κ₃ * ((1966080 : K[X]) * a1 ^ 2 * f) +
          Polynomial.C κ₃ * ((1966080 : K[X]) * a0 * a2 * f) +
          Polynomial.C κ₃ * ((3932160 : K[X]) * a0 * a1 * g) +
        H * ((12902400 : K[X]) * a0 * f ^ 4 -
            (117964800 : K[X]) * a0 ^ 2 * f ^ 2 +
            (838860800 : K[X]) * a0 ^ 3 -
            Polynomial.C κ₁₁ * ((1 : K[X])) +
            Polynomial.C κ₇ * ((480 : K[X]) * f ^ 2) -
            Polynomial.C κ₇ * ((10240 : K[X]) * a0) -
            Polynomial.C κ₃ * ((40320 : K[X]) * f ^ 4) +
            Polynomial.C κ₃ * ((737280 : K[X]) * a0 * f ^ 2) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * a0 ^ 2)))) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing twelfth-row packets -/

/-- Source-facing weight-`18` integral of a normalized aligned
scale-two `(4,10)` source: the degree-`1` row is consumed into
`M₂₀ = κ₁₁ H¹⁸` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows.  Only the terminal
degree-`0` Keller-constant row remains unused. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ : K,
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
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₀ * H ^ 33 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
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
  obtain ⟨κ₁₀, hM18⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₁₁, hM20⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀, κ₁₁,
    aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14, hM16, hM18, hM20,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

set_option maxHeartbeats 1000000 in
/-- Exact square-chamber twelfth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free form `M₂₀ = κ₁₁ H¹⁸`, the ninth face's solved `q₀` row
carrying `s₁₆`, the NEW μ-free leading divisibility carrying `s₂₅`,
the explicit peels producing `s₂₆` through `s₃₃`, the `p₀`-cubic
constant pin, and the GLOBAL `q₀`-backwire cross-tie eliminating the
`p₀`-cubic between the two pins.  The constants are preserved, not
cleared. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ μ₅ κ₁₁ : K)
      (u v s₁₆ s₂₅ s₂₆ s₂₇ s₂₈ s₂₉ s₃₀ s₃₁ s₃₂ s₃₃ : K[X]),
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
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₅ * h0 ^ 33 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (4194304 : K[X]) * q.coeff 0 =
          Polynomial.C κ * ((524288 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ₅ * ((2048 : K[X]) * p.coeff 0) -
            Polynomial.C κ₉ - s₁₆ ∧
        (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
            (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
        h0 * s₂₅ ∧
        s₂₅ + (51200 : K[X]) * (p.coeff 1) * u *
          ((187 : K[X]) * u ^ 4 - (664 : K[X]) * (p.coeff 2) * u ^ 2 +
            (432 : K[X]) * (p.coeff 2) ^ 2) * v ^ 2 +
          Polynomial.C μ * ((35840 : K[X]) * (p.coeff 2) ^ 3 * u * v) = h0 * s₂₆ ∧
        s₂₆ +
          (314572800 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) ^ 2 * v -
          Polynomial.C μ * ((349440 : K[X]) * (p.coeff 2) ^ 2 * u * v ^ 2) +
          Polynomial.C μ * ((286720 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 3) = h0 * s₂₇ ∧
        s₂₇ +
          (334233600 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * v ^ 2 +
          (209715200 : K[X]) * (p.coeff 1) ^ 3 * (p.coeff 2) * u -
          (78643200 : K[X]) * (p.coeff 0) * (p.coeff 2) ^ 2 * v ^ 2 -
          Polynomial.C μ₂ * ((6400 : K[X]) * (p.coeff 2) ^ 2 * u * v) -
          Polynomial.C μ * ((495040 : K[X]) * (p.coeff 2) * u * v ^ 3) -
          Polynomial.C μ * ((6236160 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 2 * v) +
          Polynomial.C κ₃ * ((245760 : K[X]) * (p.coeff 2) ^ 2 * v ^ 2) = h0 * s₂₈ ∧
        s₂₈ +
          (68812800 : K[X]) * (p.coeff 1) ^ 2 * v ^ 3 +
          (183500800 : K[X]) * (p.coeff 1) ^ 3 * u * v -
          (68812800 : K[X]) * (p.coeff 0) * (p.coeff 2) * v ^ 3 -
          (314572800 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2) * u * v -
          Polynomial.C μ₂ * ((35200 : K[X]) * (p.coeff 2) * u * v ^ 2) -
          Polynomial.C μ₂ * ((51200 : K[X]) * (p.coeff 1) * (p.coeff 2) ^ 2) -
          Polynomial.C μ * ((123760 : K[X]) * u * v ^ 4) -
          Polynomial.C μ * ((8547840 : K[X]) * (p.coeff 1) * (p.coeff 2) * v ^ 2) -
          Polynomial.C μ * ((6881280 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * u) +
          Polynomial.C κ₃ * ((215040 : K[X]) * (p.coeff 2) * v ^ 3) +
          Polynomial.C κ₃ * ((983040 : K[X]) * (p.coeff 1) * (p.coeff 2) * u * v) = h0 * s₂₉ ∧
        s₂₉ -
          (12902400 : K[X]) * (p.coeff 0) * v ^ 4 -
          (176947200 : K[X]) * (p.coeff 0) * (p.coeff 1) * u * v ^ 2 +
          (104857600 : K[X]) * (p.coeff 1) ^ 4 -
          (1258291200 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * (p.coeff 2) +
          Polynomial.C μ₃ * ((960 : K[X]) * (p.coeff 2) * u * v) -
          Polynomial.C μ₂ * ((13200 : K[X]) * u * v ^ 3) -
          Polynomial.C μ₂ * ((486400 : K[X]) * (p.coeff 1) * (p.coeff 2) * v) -
          Polynomial.C μ * ((1921920 : K[X]) * (p.coeff 1) * v ^ 3) -
          Polynomial.C μ * ((8601600 : K[X]) * (p.coeff 1) ^ 2 * u * v) +
          Polynomial.C μ * ((3440640 : K[X]) * (p.coeff 0) * (p.coeff 2) * u * v) +
          Polynomial.C κ₃ * ((40320 : K[X]) * v ^ 4) +
          Polynomial.C κ₃ * ((552960 : K[X]) * (p.coeff 1) * u * v ^ 2) +
          Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2)) = h0 * s₃₀ ∧
        s₃₀ -
          (629145600 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * v +
          (314572800 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 2) * v +
          Polynomial.C μ₃ * ((720 : K[X]) * u * v ^ 2) +
          Polynomial.C μ₃ * ((7680 : K[X]) * (p.coeff 1) * (p.coeff 2)) -
          Polynomial.C μ₂ * ((156800 : K[X]) * (p.coeff 1) * v ^ 2) -
          Polynomial.C μ₂ * ((409600 : K[X]) * (p.coeff 1) ^ 2 * u) +
          Polynomial.C μ * ((2580480 : K[X]) * (p.coeff 0) * u * v ^ 2) -
          Polynomial.C μ * ((9175040 : K[X]) * (p.coeff 1) ^ 3) +
          Polynomial.C μ * ((27525120 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2)) -
          Polynomial.C κ₇ * ((1280 : K[X]) * (p.coeff 2) * v) +
          Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 1) ^ 2 * v) -
          Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 0) * (p.coeff 2) * v) = h0 * s₃₁ ∧
        s₃₁ +
          (117964800 : K[X]) * (p.coeff 0) ^ 2 * v ^ 2 +
          (629145600 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 1) * u +
          Polynomial.C μ₄ * ((80 : K[X]) * u * v) +
          Polynomial.C μ₃ * ((5760 : K[X]) * (p.coeff 1) * v) +
          Polynomial.C μ₂ * ((204800 : K[X]) * (p.coeff 0) * u * v) +
          Polynomial.C μ * ((20643840 : K[X]) * (p.coeff 0) * (p.coeff 1) * v) -
          Polynomial.C κ₇ * ((480 : K[X]) * v ^ 2) -
          Polynomial.C κ₇ * ((2560 : K[X]) * (p.coeff 1) * u) -
          Polynomial.C κ₃ * ((737280 : K[X]) * (p.coeff 0) * v ^ 2) -
          Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 0) * (p.coeff 1) * u) = h0 * s₃₂ ∧
        s₃₂ +
          Polynomial.C μ₄ * ((640 : K[X]) * (p.coeff 1)) +
          Polynomial.C μ₂ * ((1638400 : K[X]) * (p.coeff 0) * (p.coeff 1)) = h0 * s₃₃ ∧
        Polynomial.C κ₁₁ =
          (838860800 : K[X]) * (p.coeff 0) ^ 3 -
            Polynomial.C κ₇ * ((10240 : K[X]) * (p.coeff 0)) -
            Polynomial.C κ₃ * ((7864320 : K[X]) * (p.coeff 0) ^ 2) - s₃₃ ∧
        Polynomial.C κ * Polynomial.C κ₁₁ =
          (6710886400 : K[X]) * p.coeff 0 * q.coeff 0 +
            Polynomial.C κ₅ * ((3276800 : K[X]) * p.coeff 0 ^ 2) +
            Polynomial.C κ₉ * ((1600 : K[X]) * p.coeff 0) +
            (1600 : K[X]) * p.coeff 0 * s₁₆ -
            Polynomial.C κ * Polynomial.C κ₃ * ((7864320 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C κ * Polynomial.C κ₇ * ((10240 : K[X]) * p.coeff 0) -
            Polynomial.C κ * s₃₃ := by
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
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
    thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
  have hcore10 :=
    alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form hM14form hM16
  obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, _ht1, _ht2, _ht3, _ht4,
    _ht5, _ht6, _ht7, hq0⟩ := alignedSquareTenth_solved_410 hh0 hcore10 hv
  obtain ⟨κ₁₁, hM20rel⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore12 :=
    alignedSquareTwelfth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM10form hM12form hM14form hM20rel
  obtain ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hd1, hd2, hd3,
    hd4, hd5, hd6, hd7, hd8, hd9, hpin⟩ :=
    alignedSquareTwelfth_solved_410 hh0 hcore12 hv
  have hcross : Polynomial.C κ * Polynomial.C κ₁₁ =
      (6710886400 : K[X]) * p.coeff 0 * q.coeff 0 +
        Polynomial.C κ₅ * ((3276800 : K[X]) * p.coeff 0 ^ 2) +
        Polynomial.C κ₉ * ((1600 : K[X]) * p.coeff 0) +
        (1600 : K[X]) * p.coeff 0 * s₁₆ -
        Polynomial.C κ * Polynomial.C κ₃ *
          ((7864320 : K[X]) * p.coeff 0 ^ 2) -
        Polynomial.C κ * Polynomial.C κ₇ *
          ((10240 : K[X]) * p.coeff 0) -
        Polynomial.C κ * s₃₃ := by
    linear_combination Polynomial.C κ * hpin -
      (1600 : K[X]) * p.coeff 0 * hq0
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, κ₁₁, u, v, s₁₆, s₂₅,
    s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hp3, hDform, hM4, hM6form,
    hM8form, hM10form, hM12form, hM14form, hM16, hM18form, hM20rel, hv,
    hq0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hpin, hcross⟩

set_option maxHeartbeats 1000000 in
/-- Exact nonsquare-chamber twelfth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free form `M₂₀ = κ₁₁ H¹⁸` (no parity kill), and the `q`-free
block identity on the fifth face's divisibility `g² - 4 p₂ = H f`
whose `H²`-part ties `κ₁₁` two levels deep. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ κ₉ κ₁₁ : K) (g f : K[X]),
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
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((3200 : K[X]) * ((143 : K[X]) * g ^ 6 - (572 : K[X]) * (p.coeff 2) * g ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * g ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * f ^ 3 +
          (51200 : K[X]) * (p.coeff 1) * g *
            ((187 : K[X]) * g ^ 4 - (664 : K[X]) * (p.coeff 2) * g ^ 2 +
              (432 : K[X]) * (p.coeff 2) ^ 2) * f ^ 2 +
          (314572800 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) ^ 2 * f +
          (209715200 : K[X]) * (p.coeff 1) ^ 3 * (p.coeff 2) * g =
          H * (-(334233600 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2) * f ^ 2 -
            (183500800 : K[X]) * (p.coeff 1) ^ 3 * g * f +
            (78643200 : K[X]) * (p.coeff 0) * (p.coeff 2) ^ 2 * f ^ 2 +
            (314572800 : K[X]) * (p.coeff 0) * (p.coeff 1) * (p.coeff 2) * g * f -
            (104857600 : K[X]) * (p.coeff 1) ^ 4 +
            (1258291200 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * (p.coeff 2) -
            Polynomial.C κ₃ * ((245760 : K[X]) * (p.coeff 2) ^ 2 * f ^ 2) -
            Polynomial.C κ₃ * ((983040 : K[X]) * (p.coeff 1) * (p.coeff 2) * g * f) -
            Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 1) ^ 2 * (p.coeff 2)) +
          H * (-(68812800 : K[X]) * (p.coeff 1) ^ 2 * f ^ 3 +
              (68812800 : K[X]) * (p.coeff 0) * (p.coeff 2) * f ^ 3 +
              (176947200 : K[X]) * (p.coeff 0) * (p.coeff 1) * g * f ^ 2 +
              (629145600 : K[X]) * (p.coeff 0) * (p.coeff 1) ^ 2 * f -
              (314572800 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 2) * f -
              (629145600 : K[X]) * (p.coeff 0) ^ 2 * (p.coeff 1) * g +
              Polynomial.C κ₇ * ((1280 : K[X]) * (p.coeff 2) * f) +
              Polynomial.C κ₇ * ((2560 : K[X]) * (p.coeff 1) * g) -
              Polynomial.C κ₃ * ((215040 : K[X]) * (p.coeff 2) * f ^ 3) -
              Polynomial.C κ₃ * ((552960 : K[X]) * (p.coeff 1) * g * f ^ 2) -
              Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 1) ^ 2 * f) +
              Polynomial.C κ₃ * ((1966080 : K[X]) * (p.coeff 0) * (p.coeff 2) * f) +
              Polynomial.C κ₃ * ((3932160 : K[X]) * (p.coeff 0) * (p.coeff 1) * g) +
            H * ((12902400 : K[X]) * (p.coeff 0) * f ^ 4 -
                (117964800 : K[X]) * (p.coeff 0) ^ 2 * f ^ 2 +
                (838860800 : K[X]) * (p.coeff 0) ^ 3 -
                Polynomial.C κ₁₁ * ((1 : K[X])) +
                Polynomial.C κ₇ * ((480 : K[X]) * f ^ 2) -
                Polynomial.C κ₇ * ((10240 : K[X]) * (p.coeff 0)) -
                Polynomial.C κ₃ * ((40320 : K[X]) * f ^ 4) +
                Polynomial.C κ₃ * ((737280 : K[X]) * (p.coeff 0) * f ^ 2) -
                Polynomial.C κ₃ * ((7864320 : K[X]) * (p.coeff 0) ^ 2))))) := by
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
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₁₀, hM180⟩ :=
    thirtyThirdPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM18rel
  obtain ⟨κ₁₁, hM20rel⟩ :=
    alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore12 :=
    alignedNonsquareTwelfth_core_410 hH hg hD0 hM4 hM60 hM100 hM12form
      hM140 hM20rel
  have hblk := alignedNonsquareTwelfth_solved_410 hH hcore12 hf
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, κ₁₁, g, f, hg, hD0, hM4, hM60, hM8form,
    hM100, hM12form, hM140, hM16, hM180, hM20rel, hf, hblk⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`1`
aligned row: the square chamber carries the chamber-free form
`M₂₀ = κ₁₁ H¹⁸` and the NEW μ-free leading divisibility carrying
`s₂₅` on the fifth face's divisibility; the nonsquare chamber carries
the same chamber-free form and the fifth face's divisibility — the
first aligned row whose integral shape is IDENTICAL in both chambers.
Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_chamberDichotomy
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
      ∃ (κ μ κ₁₁ : K) (u v s₂₅ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
          h0 * s₂₅) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₁₁ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₁₁ * H ^ 18 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, κ₁₁, u, v, s₁₆, s₂₅,
      s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hp3, hM2f, _hM4, _hM6f,
      _hM8, _hM10f, _hM12f, _hM14f, _hM16f, _hM18f, hM20f, hv, _hq0,
      hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9, _hpin,
      _hcross⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₁₁, u, v, s₂₅, hp3, hM2f,
      hM20f, hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, κ₁₁, g, f, hg, _hM2z, _hM4, _hM6z, _hM8,
      _hM10z, _hM12f, _hM14z, _hM16f, _hM18z, hM20f, hf, _hblk⟩ :=
      hpacket
    exact Or.inr ⟨hnsq, κ, κ₁₁, g, f, hg, hM20f, hf⟩

set_option maxHeartbeats 4000000 in
/-- Extended root data of the consumed degree-`1` row: at scale two
the common core has a root `a` where the previous jet dies
(`p₃(a) = 0`, `q₈` to second order), and the NEW degree-`1` content
splits by chamber.  The square chamber gains the NEW value tie as a
PURE PRODUCT KILL `u(a)⁶ v(a)³ = 0` — the first aligned root tie that
is itself a product kill — so the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)` follows DIRECTLY (via
the sixth face's product kill), plus the double unconditional peel
kills `s₂₅(a) = 0` AND `s₂₆(a) = 0`, the μ₄-loaded tie on `s₃₂`, the
`κ₁₁` value tie, the ninth face's `q₀` tie, the eighth face's `q₁`
tie, and the `κ₇`-free `q₁`-backwire combination — the first aligned
root tie linking `κ₁₁` to a solved `q`-letter.  The nonsquare
chamber's block dies at `a` and collapses on the quadratic kill to the
perfect-cube product `g(a)³ (g(a) f(a) + 8 p₁(a))³ = 0` — an
independent re-derivation of the eighth face's pin content; no new pin
is claimed.  Both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedTwelfthRow_rootData
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
      ((∃ (μ μ₂ μ₃ μ₄ κ₃ κ₅ κ₇ κ₉ κ₁₁ : K)
          (h0 u v s₉ s₁₆ s₂₅ s₂₆ s₃₂ s₃₃ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (3200 : K[X]) * ((143 : K[X]) * u ^ 6 - (572 : K[X]) * (p.coeff 2) * u ^ 4 +
              (528 : K[X]) * (p.coeff 2) ^ 2 * u ^ 2 - (64 : K[X]) * (p.coeff 2) ^ 3) * v ^ 3 =
          h0 * s₂₅ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          u.eval a ^ 6 * v.eval a ^ 3 = 0 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₂₅.eval a =
            -(39321600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2 -
            μ * ((35840 : K) * (p.coeff 2).eval a ^ 3 * u.eval a * v.eval a) ∧
          s₂₅.eval a = 0 ∧
          s₂₆.eval a =
            -(314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * v.eval a +
            μ * ((349440 : K) * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2) -
            μ * ((286720 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 3) ∧
          s₂₆.eval a = 0 ∧
          s₃₂.eval a =
            -μ₄ * ((640 : K) * (p.coeff 1).eval a) -
            μ₂ * ((1638400 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a) ∧
          κ₁₁ =
            (838860800 : K) * (p.coeff 0).eval a ^ 3 -
            κ₇ * ((10240 : K) * (p.coeff 0).eval a) -
            κ₃ * ((7864320 : K) * (p.coeff 0).eval a ^ 2) -
            s₃₃.eval a ∧
          (4194304 : K) * (q.coeff 0).eval a =
            (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
              (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
              s₁₆.eval a ∧
          (1048576 : K) * (q.coeff 1).eval a =
            s₉.eval a - (4 : K) * κ₇ * u.eval a -
              (512 : K) * κ₅ * (p.coeff 1).eval a -
              (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
              (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
              (262144 : K) * κ * (p.coeff 0).eval a *
                (p.coeff 1).eval a ∧
          u.eval a * κ₁₁ =
            (2684354560 : K) * (p.coeff 0).eval a *
                (q.coeff 1).eval a -
              (1677721600 : K) * (p.coeff 0).eval a ^ 3 * u.eval a +
              (7864320 : K) * κ₃ * (p.coeff 0).eval a ^ 2 * u.eval a +
              (1310720 : K) * κ₅ * (p.coeff 0).eval a *
                (p.coeff 1).eval a -
              (671088640 : K) * κ * (p.coeff 0).eval a ^ 2 *
                (p.coeff 1).eval a -
              (2560 : K) * (p.coeff 0).eval a * s₉.eval a -
              s₃₃.eval a * u.eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (457600 : K) * g.eval a ^ 6 * f.eval a ^ 3 -
                (1830400 : K) * (p.coeff 2).eval a * g.eval a ^ 4 * f.eval a ^ 3 +
                (9574400 : K) * (p.coeff 1).eval a * g.eval a ^ 5 * f.eval a ^ 2 +
                (1689600 : K) * (p.coeff 2).eval a ^ 2 * g.eval a ^ 2 * f.eval a ^ 3 -
                (33996800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
                (204800 : K) * (p.coeff 2).eval a ^ 3 * f.eval a ^ 3 +
                (22118400 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * g.eval a * f.eval a ^ 2 +
                (314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * f.eval a +
                (209715200 : K) * (p.coeff 1).eval a ^ 3 * (p.coeff 2).eval a * g.eval a = 0 ∧
            g.eval a ^ 3 * (g.eval a * f.eval a +
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
    have hcore9 :=
      alignedSquareNinth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form
    obtain ⟨s₅, s₆, s₇, s₈, s₉, _hn1, _hn2, _hn3, _hn4, _hn5, hq1⟩ :=
      alignedSquareNinth_solved_410 hh0 hcore9 hv
    obtain ⟨κ₉, hM16⟩ :=
      alignedTenthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore10 :=
      alignedSquareTenth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form hM14form hM16
    obtain ⟨s₁₀, s₁₁, s₁₂, s₁₃, s₁₄, s₁₅, s₁₆, _ht1, _ht2, _ht3, _ht4,
      _ht5, _ht6, _ht7, hq0⟩ :=
      alignedSquareTenth_solved_410 hh0 hcore10 hv
    obtain ⟨κ₁₁, hM20rel⟩ :=
      alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore12 :=
      alignedSquareTwelfth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM10form hM12form hM14form hM20rel
    obtain ⟨s₂₅, s₂₆, s₂₇, s₂₈, s₂₉, s₃₀, s₃₁, s₃₂, s₃₃, hd1, hd2, hd3,
      _hd4, _hd5, _hd6, _hd7, _hd8, hd9, hpin⟩ :=
      alignedSquareTwelfth_solved_410 hh0 hcore12 hv
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
    have hev1 := congrArg (fun w : K[X] => w.eval a) hd1
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev1
    rw [hroot, zero_mul] at hev1
    have hval : (102400 : K) *
        (u.eval a ^ 6 * v.eval a ^ 3) = 0 := by
      linear_combination hev1 +
        (-(355200 : K) * u.eval a ^ 4 * v.eval a ^ 3 +
      (409600 : K) * (p.coeff 2).eval a * u.eval a ^ 2 * v.eval a ^ 3 -
      (51200 : K) * (p.coeff 2).eval a ^ 2 * v.eval a ^ 3) * hkilla
    have hu6v3 : u.eval a ^ 6 * v.eval a ^ 3 = 0 :=
      (mul_eq_zero.mp hval).resolve_left (by norm_num)
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have hv3 : v.eval a ^ 3 = 0 := by
          rcases mul_eq_zero.mp hu6v3 with h6 | h3
          · exact absurd
              (pow_eq_zero_iff (by norm_num : (6 : ℕ) ≠ 0) |>.mp h6) hu
          · exact h3
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h7 : (7 : K) * μ * u.eval a ^ 3 = 0 := by
          rw [hv3] at h16
          linear_combination -h16
        have hμ0 : μ = 0 := by
          have h7u := (mul_eq_zero.mp h7).resolve_right
            (pow_ne_zero 3 hu)
          exact (mul_eq_zero.mp h7u).resolve_left (by norm_num)
        exact Or.inr ⟨hv0, hμ0⟩
    have hev2 := congrArg (fun w : K[X] => w.eval a) hd2
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev2
    rw [hroot, zero_mul] at hev2
    have hs25raw : s₂₅.eval a =
        -(39321600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2 -
          μ * ((35840 : K) * (p.coeff 2).eval a ^ 3 * u.eval a * v.eval a) := by
      linear_combination hev2 +
        (-(9574400 : K) * (p.coeff 1).eval a * u.eval a ^ 3 * v.eval a ^ 2 -
      (4300800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * u.eval a * v.eval a ^ 2) * hkilla
    have hs25kill : s₂₅.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs25raw, hu0]; ring
      · rw [hs25raw, hv0]; ring
    have hev3 := congrArg (fun w : K[X] => w.eval a) hd3
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev3
    rw [hroot, zero_mul] at hev3
    have hs26tie : s₂₆.eval a =
        -(314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * v.eval a +
          μ * ((349440 : K) * (p.coeff 2).eval a ^ 2 * u.eval a * v.eval a ^ 2) -
          μ * ((286720 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 3) := by
      linear_combination hev3
    have hs26kill : s₂₆.eval a = 0 := by
      rcases hdich with ⟨_, hp20⟩ | ⟨hv0, hμ0⟩
      · rw [hs26tie, hp20]; ring
      · rw [hs26tie, hv0, hμ0]; ring
    have hev9 := congrArg (fun w : K[X] => w.eval a) hd9
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev9
    rw [hroot, zero_mul] at hev9
    have hs32tie : s₃₂.eval a =
        -μ₄ * ((640 : K) * (p.coeff 1).eval a) -
          μ₂ * ((1638400 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a) := by
      linear_combination hev9
    have hevP := congrArg (fun w : K[X] => w.eval a) hpin
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevP
    have hk11tie : κ₁₁ =
        (838860800 : K) * (p.coeff 0).eval a ^ 3 -
          κ₇ * ((10240 : K) * (p.coeff 0).eval a) -
          κ₃ * ((7864320 : K) * (p.coeff 0).eval a ^ 2) -
        s₃₃.eval a := by
      linear_combination hevP
    have hevQ0 := congrArg (fun w : K[X] => w.eval a) hq0
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevQ0
    have hq0tie : (4194304 : K) * (q.coeff 0).eval a =
        (524288 : K) * κ * (p.coeff 0).eval a ^ 2 -
          (2048 : K) * κ₅ * (p.coeff 0).eval a - κ₉ -
          s₁₆.eval a := by
      linear_combination hevQ0
    have hevQ1 := congrArg (fun w : K[X] => w.eval a) hq1
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hevQ1
    rw [hroot, zero_mul] at hevQ1
    have hq1tie : (1048576 : K) * (q.coeff 1).eval a =
        s₉.eval a - (4 : K) * κ₇ * u.eval a -
          (512 : K) * κ₅ * (p.coeff 1).eval a -
          (6144 : K) * κ₃ * (p.coeff 0).eval a * u.eval a +
          (983040 : K) * (p.coeff 0).eval a ^ 2 * u.eval a +
          (262144 : K) * κ * (p.coeff 0).eval a *
            (p.coeff 1).eval a := by
      linear_combination hevQ1
    have hq1combo : u.eval a * κ₁₁ =
        (2684354560 : K) * (p.coeff 0).eval a * (q.coeff 1).eval a -
          (1677721600 : K) * (p.coeff 0).eval a ^ 3 * u.eval a +
          (7864320 : K) * κ₃ * (p.coeff 0).eval a ^ 2 * u.eval a +
          (1310720 : K) * κ₅ * (p.coeff 0).eval a *
            (p.coeff 1).eval a -
          (671088640 : K) * κ * (p.coeff 0).eval a ^ 2 *
            (p.coeff 1).eval a -
          (2560 : K) * (p.coeff 0).eval a * s₉.eval a -
          s₃₃.eval a * u.eval a := by
      linear_combination u.eval a * hk11tie -
        (2560 : K) * (p.coeff 0).eval a * hq1tie
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, μ₃, μ₄, κ₃, κ₅, κ₇, κ₉, κ₁₁, h0, u, v, s₉, s₁₆,
        s₂₅, s₂₆, s₃₂, s₃₃, hh0, hHsq, hroot, hp3, hv, hd1, hp3d,
        hkilla, hu6v3, hdich, hs25raw, hs25kill, hs26tie, hs26kill,
        hs32tie, hk11tie, hq0tie, hq1tie, hq1combo⟩⟩
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
    obtain ⟨κ₁₁, hM20rel⟩ :=
      alignedTwelfthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore12 :=
      alignedNonsquareTwelfth_core_410 hH hg hD0 hM4 hM60 hM100
        hM12form hM140 hM20rel
    have hblk := alignedNonsquareTwelfth_solved_410 hH hcore12 hf
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
    have hbtie :
        (457600 : K) * g.eval a ^ 6 * f.eval a ^ 3 -
          (1830400 : K) * (p.coeff 2).eval a * g.eval a ^ 4 * f.eval a ^ 3 +
          (9574400 : K) * (p.coeff 1).eval a * g.eval a ^ 5 * f.eval a ^ 2 +
          (1689600 : K) * (p.coeff 2).eval a ^ 2 * g.eval a ^ 2 * f.eval a ^ 3 -
          (33996800 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
          (204800 : K) * (p.coeff 2).eval a ^ 3 * f.eval a ^ 3 +
          (22118400 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a ^ 2 * g.eval a * f.eval a ^ 2 +
          (314572800 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a ^ 2 * f.eval a +
          (209715200 : K) * (p.coeff 1).eval a ^ 3 * (p.coeff 2).eval a * g.eval a = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hblk
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hcube : (102400 : K) * (g.eval a ^ 3 *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3) =
        0 := by
      linear_combination hbtie +
        (-(355200 : K) * g.eval a ^ 4 * f.eval a ^ 3 +
      (409600 : K) * (p.coeff 2).eval a * g.eval a ^ 2 * f.eval a ^ 3 -
      (7116800 : K) * (p.coeff 1).eval a * g.eval a ^ 3 * f.eval a ^ 2 -
      (51200 : K) * (p.coeff 2).eval a ^ 2 * f.eval a ^ 3 +
      (5529600 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a * g.eval a * f.eval a ^ 2 +
      (19660800 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 2 * f.eval a +
      (78643200 : K) * (p.coeff 1).eval a ^ 2 * (p.coeff 2).eval a * f.eval a +
      (52428800 : K) * (p.coeff 1).eval a ^ 3 * g.eval a) * hkilla
    have hprod : g.eval a ^ 3 * (g.eval a * f.eval a +
        (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp hcube).resolve_left (by norm_num)
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hprod⟩⟩

#print axioms alignedTwelfthCoefficientJacobianRow_410
#print axioms alignedTwelfthDefect_weightedDerivative_identity_410
#print axioms alignedTwelfthDefectRow_eq_zero_410
#print axioms eighteenthPowerRelation_of_weightEighteenRow_410
#print axioms alignedTwelfthDefectPowerRelation_410
#print axioms alignedSquareTwelfth_core_410
#print axioms alignedSquareTwelfth_solved_410
#print axioms alignedNonsquareTwelfth_core_410
#print axioms alignedNonsquareTwelfth_solved_410
#print axioms normalized410ScaleTwo_alignedTwelfthRow_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedTwelfthRow_rootData

end Max11DegreeRoutes
