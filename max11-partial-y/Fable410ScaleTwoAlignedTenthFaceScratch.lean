import Fable410ScaleTwoAlignedNinthFaceScratch

/-! # Tenth aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedNinthFaceScratch` consumed the degree-`3`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the
chamber-free weight-`15` first integral `M₁₆ = κ₉ H¹⁵` of the tenth
defect, the seven-deep square peel carrying `s₁₀` through `s₁₆`, and
the solved constant coefficient `q₀`.  This file consumes the next
unused aligned row, the degree-`2` Jacobian coefficient — the LAST
aligned row above the degree-`1`/degree-`0` tail, and the FIRST with
no new letter at all: it sees `q₀` through `q₀'` only (cofactor
`3 p₃`), `q₁` through its value and derivative, and `q₂`, `q₃` through
the derivative pairings, and every one of these letters was already
consumed by a previous face (internal names `alignedEleventh*`).

At the common source level, modulo the face `N = 0` and the consumed
degree-`11` through degree-`3` brackets of `M₂`, `M₄`, `M₆`, `M₈`,
`M₁₀`, `M₁₂`, `M₁₄`, and `M₁₆`, the degree-`2` row is the weighted
derivative of the cleared eleventh defect

`M₁₈ = 125829120 p₀² p₁ H¹⁶ - 62914560 (p₀² p₂ p₃ + p₀ p₁² p₃
  + p₀ p₁ p₂²) H¹⁴ - 20971520 p₁³ p₂ H¹⁴ + 15728640 p₀² p₃³ H¹²
  + 94371840 p₀ p₁ p₂ p₃² H¹² + 31457280 p₀ p₂³ p₃ H¹²
  + 15728640 p₁³ p₃² H¹² + 47185920 p₁² p₂² p₃ H¹²
  + 7864320 p₁ p₂⁴ H¹² - 19660800 p₀ p₁ p₃⁴ H¹⁰
  - 39321600 (p₀ p₂² p₃³ + p₁² p₂ p₃³ + p₁ p₂³ p₃²) H¹⁰
  - 3932160 p₂⁵ p₃ H¹⁰ + 13762560 p₀ p₂ p₃⁵ H⁸ + 6881280 p₁² p₃⁵ H⁸
  + 34406400 p₁ p₂² p₃⁴ H⁸ + 11468800 p₂⁴ p₃³ H⁸ - 1474560 p₀ p₃⁷ H⁶
  - 10321920 p₁ p₂ p₃⁶ H⁶ - 10321920 p₂³ p₃⁵ H⁶ + 1013760 p₁ p₃⁸ H⁴
  + 4055040 p₂² p₃⁷ H⁴ - 732160 p₂ p₃⁹ H² + 49920 p₃¹¹
  - (32 p₂ H² - 12 p₃²) M₁₄ - (512 p₁ H⁴ - 256 p₂ p₃ H² + 64 p₃³) M₁₂
  - (3072 p₀ H⁶ - 768 p₁ p₃ H⁴ - 384 p₂² H⁴ + 480 p₂ p₃² H²
    - 90 p₃⁴) M₁₀
  - (81920 p₀ p₂ H⁸ + 40960 p₁² H⁸ - 30720 p₀ p₃² H⁶
    - 61440 p₁ p₂ p₃ H⁶ - 10240 p₂³ H⁶ + 17920 p₁ p₃³ H⁴
    + 26880 p₂² p₃² H⁴ - 12320 p₂ p₃⁴ H² + 1540 p₃⁶) M₆
  - (786432 p₀ p₁ H¹⁰ - 393216 p₀ p₂ p₃ H⁸ - 196608 p₁² p₃ H⁸
    - 196608 p₁ p₂² H⁸ + 98304 p₀ p₃³ H⁶ + 294912 p₁ p₂ p₃² H⁶
    + 98304 p₂³ p₃ H⁶ - 61440 p₁ p₃⁴ H⁴ - 122880 p₂² p₃³ H⁴
    + 43008 p₂ p₃⁵ H² - 4608 p₃⁷) M₄
  - (5505024 p₀² H¹² - 2752512 p₀ p₁ p₃ H¹⁰ - 1376256 p₀ p₂² H¹⁰
    - 1376256 p₁² p₂ H¹⁰ + 1720320 p₀ p₂ p₃² H⁸ + 860160 p₁² p₃² H⁸
    + 1720320 p₁ p₂² p₃ H⁸ + 143360 p₂⁴ H⁸ - 322560 p₀ p₃⁴ H⁶
    - 1290240 p₁ p₂ p₃³ H⁶ - 645120 p₂³ p₃² H⁶ + 209664 p₁ p₃⁵ H⁴
    + 524160 p₂² p₃⁴ H⁴ - 148512 p₂ p₃⁶ H² + 13923 p₃⁸) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect whose factored head carries NO `q`-letter and NO `κ`-module at
all (`M₁₆` and `M₈` do not even appear among the corrections:
`d₁₆ = d₈ = 0`, and the whole `q`/`κ`-content of the expanded defect
flows through the corrections `M₂`, `M₄`, `M₆`, `M₁₀`, `M₁₂`, `M₁₄`) —
via the exact multiplier identity

`67108864 H¹⁶ · row₂ = (2 H M₁₈' - 33 M₁₈ H')
  + 48 p₃ (H M₁₆' - 15 M₁₆ H')
  + (96 p₂ H² + 12 p₃²) (2 H M₁₄' - 27 M₁₄ H')
  + (1536 p₁ H⁴ + 768 p₂ p₃ H² - 64 p₃³) (H M₁₂' - 12 M₁₂ H')
  + (3072 p₀ H⁶ + 2304 p₁ p₃ H⁴ + 1152 p₂² H⁴ - 288 p₂ p₃² H²
    + 30 p₃⁴) (2 H M₁₀' - 21 M₁₀ H')
  + (98304 p₀ p₃ H⁶ + 98304 p₁ p₂ H⁶) (H M₈' - 9 M₈ H')
  + (245760 p₀ p₂ H⁸ + 122880 p₁² H⁸ + 30720 p₀ p₃² H⁶
    + 61440 p₁ p₂ p₃ H⁶ + 10240 p₂³ H⁶ - 7680 p₁ p₃³ H⁴
    - 11520 p₂² p₃² H⁴ + 3360 p₂ p₃⁴ H² - 308 p₃⁶)
    (2 H M₆' - 15 M₆ H')
  + (2359296 p₀ p₁ H¹⁰ + 1179648 p₀ p₂ p₃ H⁸ + 589824 p₁² p₃ H⁸
    + 589824 p₁ p₂² H⁸ - 98304 p₀ p₃³ H⁶ - 294912 p₁ p₂ p₃² H⁶
    - 98304 p₂³ p₃ H⁶ + 36864 p₁ p₃⁴ H⁴ + 73728 p₂² p₃³ H⁴
    - 18432 p₂ p₃⁵ H² + 1536 p₃⁷) (H M₄' - 6 M₄ H')
  + (5505024 p₀² H¹² + 8257536 p₀ p₁ p₃ H¹⁰ + 4128768 p₀ p₂² H¹⁰
    + 4128768 p₁² p₂ H¹⁰ - 1032192 p₀ p₂ p₃² H⁸ - 516096 p₁² p₃² H⁸
    - 1032192 p₁ p₂² p₃ H⁸ - 86016 p₂⁴ H⁸ + 107520 p₀ p₃⁴ H⁶
    + 430080 p₁ p₂ p₃³ H⁶ + 215040 p₂³ p₃² H⁶ - 48384 p₁ p₃⁵ H⁴
    - 120960 p₂² p₃⁴ H⁴ + 26208 p₂ p₃⁶ H² - 1989 p₃⁸)
    (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁶ H¹⁶`, `row₂ = p₂' q₁ + 2 p₁' q₂ + 3 p₀' q₃
- (3 p₃ q₀' + 2 p₂ q₁' + p₁ q₂')` (unique solution of the factored
cofactor system: nullspace dimension `12` = the multiplier solution
plus `11` pure re-presentation gauges that leave the expanded defect
unchanged).  The correction module is EMPTY for the FIFTH row in a
row, and the entire `q₀'`-content of the row is carried by the `M₁₆`
bracket with cofactor `48 p₃`.  On the aligned face every previous
bracket vanishes, so `2 H M₁₈' = 33 M₁₈ H'` and the squared
weight-`33/2` first integral

`M₁₈² = κ₁₀ H³³`

holds for a constant `κ₁₀` — the FIFTH regeneration of the odd-power
discriminator shape (`H⁹, H¹⁵, H²¹, H²⁷, H³³`).  The chambers split
honestly on parity.  The chamber core, after cancelling `h₀²²` resp.
`H¹¹`, is a quartic-cofactor cube plus a `p₁`-loaded square:

`1280 w (39 w⁴ - 104 p₂ w² + 48 p₂²) (w² - 4 p₂)³
  + 30720 h p₁ (33 w⁴ - 72 p₂ w² + 16 p₂²) (w² - 4 p₂)²`
  (`h = h₀²` resp. `H`)

and — because every `q`-letter of the row was already solved — the
whole relation is `q`-FREE in both chambers, and `κ`, `κ₅`, `κ₉` drop
out entirely (the first aligned row blind to them).

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`, `M₁₄ = μ₄ h₀²⁷`,
  `M₁₈ = μ₅ h₀³³` with `μ₅² = κ₁₀` (honest residual): on the consumed
  divisibility `u² - 4 p₂ = h₀ v` the peel is EIGHT deep — the deepest
  aligned peel: the NEW μ-loaded OCTIC divisibility
  `1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) v³ - μ (13923 u⁸
  - 148512 p₂ u⁶ + 524160 p₂² u⁴ - 645120 p₂³ u² + 143360 p₂⁴)
  = h₀ s₁₇` — self-similar to the sixth- through ninth-face
  divisibilities one level down — then the explicit peels producing
  `s₁₈` through `s₂₄` (`s₂₂` is loaded with `μ₄`), and — with no
  letter left to solve — the FIRST aligned CONSTANT PIN

  `C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`

  — the row pins the fresh constant `μ₅` (hence `κ₁₀ = μ₅²`) globally
  against the peel letters, forcing the right side to be constant.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`,
  `M₁₂ = κ₇ H¹²`: the odd exponent forces the parity kill `κ₁₀ = 0`
  and `M₁₈ ≡ 0`.  On the consumed divisibility `g² - 4 p₂ = H f` the
  row yields the `q`-free block identity
  `1280 g (39 g⁴ - 104 p₂ g² + 48 p₂²) f³ + 30720 p₁ (33 g⁴
  - 72 p₂ g² + 16 p₂²) f² + 3932160 p₁² g³ f
  + 5242880 p₁³ (3 g² - 4 p₂) = H · (...)` — the first aligned
  nonsquare row consuming NO letter: a pure constraint among the
  descent data.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie `4096 u(a)⁵ v(a)³ = 7 μ u(a)⁸`, whose clash with the
sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a
factor-`255` mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`; on it `s₁₇(a) = 0`
unconditionally, and the ties `s₁₇(a) = -491520 p₁ u⁴ v²`,
`s₁₈(a) = -3932160 p₁² u³ v - 5376 μ p₁ u⁵ - 20 μ₂ u⁶`, the
μ₄-loaded tie `s₂₂(a) = (98304 κ₃ p₀ + 64 κ₇ - 15728640 p₀²) u v
- 2752512 μ p₀ p₁ u - 10240 μ₂ p₀ u² + 40960 μ₂ p₁² - 768 μ₃ p₁ u
- 4 μ₄ u²`, and the `μ₅` value tie
`μ₅ = s₂₄(a) - 5505024 μ p₀(a)² - 3072 μ₃ p₀(a)` — the first aligned
root tie that sees `μ₅` — follow.  The nonsquare chamber's block dies
at `a` and collapses on the quadratic kill to the PERFECT-CUBE PRODUCT

`g(a)² · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content
as a product kill with a `g²`-cofactor (this row alone forces
`g(a) = 0` or the pin; no new pin is claimed beyond the eighth face's).

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`, `dvd_of_sq_dvd_sq_poly`,
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, the sixth-face divisibility carrying `s`, and the
chamber form/kill quotients of the odd rows.  The weight-`33/2`
Wronskian quotient
`thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410` and its
chamber quotients are new but generic.

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₁₇ = 0`, `μ = 0` through `μ₅ = 0`, `κ = 0` through
`κ₁₀ = 0`) are not excluded, and the constants are preserved where not
previously forced (`κ₄ = κ₆ = κ₈ = 0` and now `κ₁₀ = 0` are forced in
the nonsquare chamber only; the square chamber pins `μ₅` against the
peel letters but does not clear it).  `p₀, p₁, p₂` are constrained
only through the solved forms, the divisibilities, and the root ties.
The aligned Jacobian tower now has ONLY the degree-`1`/degree-`0`
tail left unused: the degree-`1` row
`p₁' q₁ + 2 p₀' q₂ - (2 p₂ q₀' + p₁ q₁')` and the terminal degree-`0`
row `p₀' q₁ - p₁ q₀'`; the next unused aligned row is the degree-`1`
Jacobian coefficient.  No total-degree or twice-prime theorem is used,
and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`2` Keller coefficient on the aligned face -/

/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`2` Jacobian coefficient, the first
aligned row with no new letter — `q₀` enters through `q₀'` with
cofactor `3 p₃`, and `p₄` does not appear at all.  It is derived
directly from the Keller bracket. -/
theorem alignedEleventhCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
      ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 2) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (2 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC2, hC3]
  linear_combination hcoeff

/-! ## Aligned eleventh defect -/

set_option maxHeartbeats 800000 in
/-- Cleared eleventh defect of the degree-`2` aligned `(4,10)` row,
kept in factored form through the third through tenth defects.  Every
monomial has exact `H`-weight `33/2`.  The factored head is PURE in
the `p`-letters: no `q`-letter and no `κ`-module at all, and neither
`M₈` nor `M₁₆` appears among the corrections — the first aligned
defect with an empty head module. -/
def alignedEleventhDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (125829120 : K[X]) * H ^ 16 * a0 ^ 2 * a1 -
    (20971520 : K[X]) * H ^ 14 * a1 ^ 3 * a2 -
    (62914560 : K[X]) * H ^ 14 * a0 * a1 * a2 ^ 2 -
    (62914560 : K[X]) * H ^ 14 * a0 * a1 ^ 2 * a3 -
    (62914560 : K[X]) * H ^ 14 * a0 ^ 2 * a2 * a3 +
    (7864320 : K[X]) * H ^ 12 * a1 * a2 ^ 4 +
    (47185920 : K[X]) * H ^ 12 * a1 ^ 2 * a2 ^ 2 * a3 +
    (15728640 : K[X]) * H ^ 12 * a1 ^ 3 * a3 ^ 2 +
    (31457280 : K[X]) * H ^ 12 * a0 * a2 ^ 3 * a3 +
    (94371840 : K[X]) * H ^ 12 * a0 * a1 * a2 * a3 ^ 2 +
    (15728640 : K[X]) * H ^ 12 * a0 ^ 2 * a3 ^ 3 -
    (3932160 : K[X]) * H ^ 10 * a2 ^ 5 * a3 -
    (39321600 : K[X]) * H ^ 10 * a1 * a2 ^ 3 * a3 ^ 2 -
    (39321600 : K[X]) * H ^ 10 * a1 ^ 2 * a2 * a3 ^ 3 -
    (39321600 : K[X]) * H ^ 10 * a0 * a2 ^ 2 * a3 ^ 3 -
    (19660800 : K[X]) * H ^ 10 * a0 * a1 * a3 ^ 4 +
    (11468800 : K[X]) * H ^ 8 * a2 ^ 4 * a3 ^ 3 +
    (34406400 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 ^ 4 +
    (6881280 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 5 +
    (13762560 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 5 -
    (10321920 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 5 -
    (10321920 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 6 -
    (1474560 : K[X]) * H ^ 6 * a0 * a3 ^ 7 +
    (4055040 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 7 +
    (1013760 : K[X]) * H ^ 4 * a1 * a3 ^ 8 -
    (732160 : K[X]) * H ^ 2 * a2 * a3 ^ 9 + (49920 : K[X]) * a3 ^ 11 -
    ((32 : K[X]) * H ^ 2 * a2 - (12 : K[X]) * a3 ^ 2) *
      alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ -
    ((512 : K[X]) * H ^ 4 * a1 - (256 : K[X]) * H ^ 2 * a2 * a3 +
      (64 : K[X]) * a3 ^ 3) *
      alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ -
    ((3072 : K[X]) * H ^ 6 * a0 - (384 : K[X]) * H ^ 4 * a2 ^ 2 -
      (768 : K[X]) * H ^ 4 * a1 * a3 + (480 : K[X]) * H ^ 2 * a2 * a3 ^ 2 -
      (90 : K[X]) * a3 ^ 4) *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    ((40960 : K[X]) * H ^ 8 * a1 ^ 2 + (81920 : K[X]) * H ^ 8 * a0 * a2 -
      (10240 : K[X]) * H ^ 6 * a2 ^ 3 -
      (61440 : K[X]) * H ^ 6 * a1 * a2 * a3 -
      (30720 : K[X]) * H ^ 6 * a0 * a3 ^ 2 +
      (26880 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 2 +
      (17920 : K[X]) * H ^ 4 * a1 * a3 ^ 3 -
      (12320 : K[X]) * H ^ 2 * a2 * a3 ^ 4 + (1540 : K[X]) * a3 ^ 6) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((786432 : K[X]) * H ^ 10 * a0 * a1 -
      (196608 : K[X]) * H ^ 8 * a1 * a2 ^ 2 -
      (196608 : K[X]) * H ^ 8 * a1 ^ 2 * a3 -
      (393216 : K[X]) * H ^ 8 * a0 * a2 * a3 +
      (98304 : K[X]) * H ^ 6 * a2 ^ 3 * a3 +
      (294912 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 +
      (98304 : K[X]) * H ^ 6 * a0 * a3 ^ 3 -
      (122880 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 -
      (61440 : K[X]) * H ^ 4 * a1 * a3 ^ 4 +
      (43008 : K[X]) * H ^ 2 * a2 * a3 ^ 5 - (4608 : K[X]) * a3 ^ 7) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((5505024 : K[X]) * H ^ 12 * a0 ^ 2 -
      (1376256 : K[X]) * H ^ 10 * a1 ^ 2 * a2 -
      (1376256 : K[X]) * H ^ 10 * a0 * a2 ^ 2 -
      (2752512 : K[X]) * H ^ 10 * a0 * a1 * a3 +
      (143360 : K[X]) * H ^ 8 * a2 ^ 4 +
      (1720320 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 +
      (860160 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 +
      (1720320 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 -
      (645120 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 -
      (1290240 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 -
      (322560 : K[X]) * H ^ 6 * a0 * a3 ^ 4 +
      (524160 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 +
      (209664 : K[X]) * H ^ 4 * a1 * a3 ^ 5 -
      (148512 : K[X]) * H ^ 2 * a2 * a3 ^ 6 + (13923 : K[X]) * a3 ^ 8) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`2` Jacobian expression with the
weight-`33/2` bracket of `M₁₈`.  The corrections are the consumed
degree-`10` through degree-`3` brackets of `M₂` through `M₁₆`: neither
the aligned-face residual `N` nor the degree-`11` relation `R`
appears — the correction module is empty for the fifth row in a row —
and the `M₁₆` bracket carries the row's entire `q₀'`-content with
cofactor `48 p₃`.  Every correction vanishes on the aligned face. -/
theorem alignedEleventhDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (67108864 : K[X]) * H ^ 16 *
        (a2.derivative * b1 +
          a1.derivative * (b2 * (2 : K[X])) +
          a0.derivative * (b3 * (3 : K[X])) -
        ((a3 * (3 : K[X])) * b0.derivative +
          (a2 * (2 : K[X])) * b1.derivative +
          a1 * b2.derivative)) =
      ((2 : K[X]) * H *
          (alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (33 : K[X]) *
          alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (48 : K[X]) * a3 *
          (H * (alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6
              b7 κ).derivative -
            (15 : K[X]) *
              alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7
                κ * H.derivative) +
        ((96 : K[X]) * H ^ 2 * a2 + (12 : K[X]) * a3 ^ 2) *
          ((2 : K[X]) * H *
              (alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
                κ).derivative -
            (27 : K[X]) *
              alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((1536 : K[X]) * H ^ 4 * a1 + (768 : K[X]) * H ^ 2 * a2 * a3 -
            (64 : K[X]) * a3 ^ 3) *
          (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
              κ).derivative -
            (12 : K[X]) *
              alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((3072 : K[X]) * H ^ 6 * a0 + (1152 : K[X]) * H ^ 4 * a2 ^ 2 +
            (2304 : K[X]) * H ^ 4 * a1 * a3 -
            (288 : K[X]) * H ^ 2 * a2 * a3 ^ 2 + (30 : K[X]) * a3 ^ 4) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((98304 : K[X]) * H ^ 6 * a1 * a2 +
            (98304 : K[X]) * H ^ 6 * a0 * a3) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((122880 : K[X]) * H ^ 8 * a1 ^ 2 +
            (245760 : K[X]) * H ^ 8 * a0 * a2 +
            (10240 : K[X]) * H ^ 6 * a2 ^ 3 +
            (61440 : K[X]) * H ^ 6 * a1 * a2 * a3 +
            (30720 : K[X]) * H ^ 6 * a0 * a3 ^ 2 -
            (11520 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 2 -
            (7680 : K[X]) * H ^ 4 * a1 * a3 ^ 3 +
            (3360 : K[X]) * H ^ 2 * a2 * a3 ^ 4 - (308 : K[X]) * a3 ^ 6) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((2359296 : K[X]) * H ^ 10 * a0 * a1 +
            (589824 : K[X]) * H ^ 8 * a1 * a2 ^ 2 +
            (589824 : K[X]) * H ^ 8 * a1 ^ 2 * a3 +
            (1179648 : K[X]) * H ^ 8 * a0 * a2 * a3 -
            (98304 : K[X]) * H ^ 6 * a2 ^ 3 * a3 -
            (294912 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 2 -
            (98304 : K[X]) * H ^ 6 * a0 * a3 ^ 3 +
            (73728 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 3 +
            (36864 : K[X]) * H ^ 4 * a1 * a3 ^ 4 -
            (18432 : K[X]) * H ^ 2 * a2 * a3 ^ 5 + (1536 : K[X]) * a3 ^ 7) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((5505024 : K[X]) * H ^ 12 * a0 ^ 2 +
            (4128768 : K[X]) * H ^ 10 * a1 ^ 2 * a2 +
            (4128768 : K[X]) * H ^ 10 * a0 * a2 ^ 2 +
            (8257536 : K[X]) * H ^ 10 * a0 * a1 * a3 -
            (86016 : K[X]) * H ^ 8 * a2 ^ 4 -
            (1032192 : K[X]) * H ^ 8 * a1 * a2 ^ 2 * a3 -
            (516096 : K[X]) * H ^ 8 * a1 ^ 2 * a3 ^ 2 -
            (1032192 : K[X]) * H ^ 8 * a0 * a2 * a3 ^ 2 +
            (215040 : K[X]) * H ^ 6 * a2 ^ 3 * a3 ^ 2 +
            (430080 : K[X]) * H ^ 6 * a1 * a2 * a3 ^ 3 +
            (107520 : K[X]) * H ^ 6 * a0 * a3 ^ 4 -
            (120960 : K[X]) * H ^ 4 * a2 ^ 2 * a3 ^ 4 -
            (48384 : K[X]) * H ^ 4 * a1 * a3 ^ 5 +
            (26208 : K[X]) * H ^ 2 * a2 * a3 ^ 6 - (1989 : K[X]) * a3 ^ 8) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) *
              alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [alignedEleventhDefect410, alignedTenthDefect410,
    alignedNinthDefect410, alignedEighthDefect410, alignedSeventhDefect410,
    alignedSixthDefect410, alignedFifthDefect410, alignedFourthDefect410,
    alignedThirdDefect410,
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
degree-`3` rows, the degree-`2` row is the weighted derivative
`2 H M₁₈' - 33 M₁₈ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (33 : K[X]) *
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_410 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  rw [hC2, hC3] at hrow
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
  have hid := alignedEleventhDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 0)
    (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10, hB12, hB14, hB16] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Squared weight-`33/2` polynomial first integral -/

/-- Generic Wronskian quotient for the weight-`33/2` bracket: over a
characteristic-zero field, `2 H D' - 33 D H' = 0` forces
`D² = C c * H³³`. -/
theorem thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410
    {K : Type*} [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (33 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 33 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (33 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC33 : Polynomial.C (33 : K) = (33 : K[X]) :=
      Polynomial.C_eq_natCast 33
    rw [hC2, hC33]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 33) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (33 : K) * H ^ (33 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 33 =
          D * H ^ 32 *
            (Polynomial.C (33 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 33 hH) hW

/-- Squared weight-`33/2` polynomial first integral of the aligned
`(4,10)` eleventh defect: `M₁₈² = κ₁₀ H³³` — the odd-power
discriminator shape regenerated a FIFTH time, one level below the even
weight-`15` shape of the degree-`3` row. -/
theorem alignedEleventhDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 33 :=
  thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410 hH
    (alignedEleventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Chamber quotients of the thirty-third-power relation -/

/-- In the square chamber `H = h₀²` the thirty-third-power relation
resolves to the literal half-integral form `D = C μ₅ * h₀³³` with
`μ₅² = c`; the scalar `μ₅` is an honest residual and is not cleared. -/
theorem thirtyThirdPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 33) :
    ∃ μ₅ : K, μ₅ ^ 2 = c ∧ D = Polynomial.C μ₅ * h0 ^ 33 := by
  have hdvd : (h0 ^ 33) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h66 := hrel
    rw [hF, hHsq] at h66
    apply mul_left_cancel₀ (pow_ne_zero 66 hh0)
    linear_combination h66
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₅, hμ₅⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₅, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₅ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₅, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₅]
    ring

/-- Parity kill in the nonsquare chamber: the odd exponent of the
thirty-third-power relation forces its constant to vanish, and with it
the whole eleventh defect. -/
theorem thirtyThirdPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 33) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 16) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 32 hH)
    have h32 := hrel
    rw [hG] at h32
    linear_combination h32
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C c := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hc : c = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [ha, zero_mul] at hev
    exact hev.symm
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

/-! ## Square chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared square-core form of the eleventh defect relation:
cancelling `h₀²²` from `M₁₈ = μ₅ h₀³³` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
`M₁₄ = μ₄ h₀²⁷` exposes the `h₀`-free core
`1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) (u² - 4 p₂)³
+ 30720 h₀² p₁ (33 u⁴ - 72 p₂ u² + 16 p₂²) (u² - 4 p₂)²` carried by
`h₀³` against the explicit quotient, whose leading block is the
μ-loaded octic `13923 u⁸ - 148512 p₂ u⁶ + 524160 p₂² u⁴
- 645120 p₂³ u² + 143360 p₂⁴`.  Neither `M₈` nor `M₁₆` enters, and
the whole relation is `q`-free and `κ`/`κ₅`/`κ₉`-free. -/
theorem alignedSquareEleventh_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ μ₃ κ₇ μ₄ μ₅ : K}
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
    (hM18 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C μ₅ * h0 ^ 33) :
    (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 - (104 : K[X]) * a2 * u ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * h0 ^ 2 * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
              (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
              (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
              (143360 : K[X]) * a2 ^ 4) +
          h0 * ((1536 : K[X]) * u *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  u ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (2560 : K[X]) * a1 ^ 2 * u ^ 2 *
                (u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 2 *
            (Polynomial.C μ *
                ((209664 : K[X]) * a1 * u ^ 5 -
                  (1290240 : K[X]) * a1 * a2 * u ^ 3 +
                  (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
              Polynomial.C μ₂ *
                ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
                  (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
                  (10240 : K[X]) * a2 ^ 3)) +
          h0 ^ 3 * ((4096 : K[X]) * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                u ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2))) +
          h0 ^ 4 *
            (Polynomial.C μ *
                ((1720320 : K[X]) * a0 * a2 * u ^ 2 -
                  (322560 : K[X]) * a0 * u ^ 4 -
                  (1376256 : K[X]) * a0 * a2 ^ 2 +
                  (860160 : K[X]) * a1 ^ 2 * u ^ 2 -
                  (1376256 : K[X]) * a1 ^ 2 * a2) +
              Polynomial.C μ₂ *
                ((17920 : K[X]) * a1 * u ^ 3 -
                  (61440 : K[X]) * a1 * a2 * u) +
              Polynomial.C μ₃ *
                ((480 : K[X]) * a2 * u ^ 2 - (90 : K[X]) * u ^ 4 -
                  (384 : K[X]) * a2 ^ 2)) +
          h0 ^ 5 * ((64 : K[X]) * u *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (u ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2)) +
          h0 ^ 6 *
            (Polynomial.C μ₂ *
                ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
                  (40960 : K[X]) * a1 ^ 2) -
              Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
              Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
              Polynomial.C μ₄ *
                ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2)) +
          h0 ^ 7 *
            (Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
              Polynomial.C κ₇ * ((512 : K[X]) * a1) -
              (125829120 : K[X]) * a0 ^ 2 * a1) +
          h0 ^ 8 *
            (Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
              Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
              Polynomial.C μ₅)) := by
  have hM18' := hM18
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM14, hM12, hM10, hM6, hM4, hM2, hHsq, hp3] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 22 hh0)
  linear_combination hM18'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`2` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains
`h₀³`, and the peel is EIGHT deep: the NEW μ-loaded octic divisibility
`1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) v³ - μ (13923 u⁸ - 148512 p₂ u⁶
+ 524160 p₂² u⁴ - 645120 p₂³ u² + 143360 p₂⁴) = h₀ s₁₇`, the explicit
peels producing `s₁₈` through `s₂₄` (`s₂₂` is loaded with `μ₄`), and —
with no letter left to solve — the FIRST aligned CONSTANT PIN
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`. -/
theorem alignedSquareEleventh_solved_410 {K : Type*} [Field K]
    [CharZero K] {h0 u v a0 a1 a2 : K[X]} {μ κ₃ μ₂ μ₃ κ₇ μ₄ μ₅ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
              (104 : K[X]) * a2 * u ^ 2 + (48 : K[X]) * a2 ^ 2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (30720 : K[X]) * h0 ^ 2 * a1 *
            ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
              (16 : K[X]) * a2 ^ 2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
                (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
                (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
                (143360 : K[X]) * a2 ^ 4) +
            h0 * ((1536 : K[X]) * u *
              (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
                (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                    u ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
                (2560 : K[X]) * a1 ^ 2 * u ^ 2 *
                  (u ^ 2 - (4 : K[X]) * a2))) +
            h0 ^ 2 *
              (Polynomial.C μ *
                  ((209664 : K[X]) * a1 * u ^ 5 -
                    (1290240 : K[X]) * a1 * a2 * u ^ 3 +
                    (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
                Polynomial.C μ₂ *
                  ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
                    (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
                    (10240 : K[X]) * a2 ^ 3)) +
            h0 ^ 3 * ((4096 : K[X]) * a1 *
              (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                  (u ^ 2 - (4 : K[X]) * a2) ^ 2 +
                ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                  u ^ 2 * (u ^ 2 - (4 : K[X]) * a2) -
                (1280 : K[X]) * a1 ^ 2 *
                  ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2))) +
            h0 ^ 4 *
              (Polynomial.C μ *
                  ((1720320 : K[X]) * a0 * a2 * u ^ 2 -
                    (322560 : K[X]) * a0 * u ^ 4 -
                    (1376256 : K[X]) * a0 * a2 ^ 2 +
                    (860160 : K[X]) * a1 ^ 2 * u ^ 2 -
                    (1376256 : K[X]) * a1 ^ 2 * a2) +
                Polynomial.C μ₂ *
                  ((17920 : K[X]) * a1 * u ^ 3 -
                    (61440 : K[X]) * a1 * a2 * u) +
                Polynomial.C μ₃ *
                  ((480 : K[X]) * a2 * u ^ 2 - (90 : K[X]) * u ^ 4 -
                    (384 : K[X]) * a2 ^ 2)) +
            h0 ^ 5 * ((64 : K[X]) * u *
              ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                  Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2) *
                  (u ^ 2 - (4 : K[X]) * a2) +
                ((983040 : K[X]) * a0 -
                  Polynomial.C κ₃ * (3072 : K[X])) * a1 ^ 2)) +
            h0 ^ 6 *
              (Polynomial.C μ₂ *
                  ((81920 : K[X]) * a0 * a2 -
                    (30720 : K[X]) * a0 * u ^ 2 +
                    (40960 : K[X]) * a1 ^ 2) -
                Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
                Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
                Polynomial.C μ₄ *
                  ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2)) +
            h0 ^ 7 *
              (Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
                Polynomial.C κ₇ * ((512 : K[X]) * a1) -
                (125829120 : K[X]) * a0 ^ 2 * a1) +
            h0 ^ 8 *
              (Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
                Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
                Polynomial.C μ₅)))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₁₇ s₁₈ s₁₉ s₂₀ s₂₁ s₂₂ s₂₃ s₂₄ : K[X],
      (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
            (104 : K[X]) * a2 * u ^ 2 + (48 : K[X]) * a2 ^ 2) * v ^ 3 -
          Polynomial.C μ *
            ((13923 : K[X]) * u ^ 8 - (148512 : K[X]) * a2 * u ^ 6 +
              (524160 : K[X]) * a2 ^ 2 * u ^ 4 -
              (645120 : K[X]) * a2 ^ 3 * u ^ 2 +
              (143360 : K[X]) * a2 ^ 4) = h0 * s₁₇ ∧
      s₁₇ + (30720 : K[X]) * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) * v ^ 2 = h0 * s₁₈ ∧
      s₁₈ + (3932160 : K[X]) * a1 ^ 2 * u ^ 3 * v -
          Polynomial.C μ *
            ((209664 : K[X]) * a1 * u ^ 5 -
              (1290240 : K[X]) * a1 * a2 * u ^ 3 +
              (1720320 : K[X]) * a1 * a2 ^ 2 * u) -
          Polynomial.C μ₂ *
            ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
              (26880 : K[X]) * a2 ^ 2 * u ^ 2 -
              (10240 : K[X]) * a2 ^ 3) = h0 * s₁₉ ∧
      s₁₉ - (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            u ^ 2 - (2949120 : K[X]) * a1 ^ 2) * u * v ^ 2 +
          (5242880 : K[X]) * a1 ^ 3 *
            ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) = h0 * s₂₀ ∧
      s₂₀ - ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
            u * v ^ 3 -
          ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
            a1 * u ^ 2 * v +
          Polynomial.C μ *
            ((322560 : K[X]) * a0 * u ^ 4 -
              (1720320 : K[X]) * a0 * a2 * u ^ 2 +
              (1376256 : K[X]) * a0 * a2 ^ 2 -
              (860160 : K[X]) * a1 ^ 2 * u ^ 2 +
              (1376256 : K[X]) * a1 ^ 2 * a2) -
          Polynomial.C μ₂ *
            ((17920 : K[X]) * a1 * u ^ 3 -
              (61440 : K[X]) * a1 * a2 * u) +
          Polynomial.C μ₃ *
            ((90 : K[X]) * u ^ 4 - (480 : K[X]) * a2 * u ^ 2 +
              (384 : K[X]) * a2 ^ 2) = h0 * s₂₁ ∧
      s₂₁ - ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
            a1 * v ^ 2 -
          ((62914560 : K[X]) * a0 -
            Polynomial.C κ₃ * (196608 : K[X])) * a1 ^ 2 * u =
        h0 * s₂₂ ∧
      s₂₂ - (Polynomial.C κ₃ * ((98304 : K[X]) * a0) +
            Polynomial.C κ₇ * (64 : K[X]) -
            (15728640 : K[X]) * a0 ^ 2) * u * v +
          Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) -
          Polynomial.C μ₂ *
            ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
              (40960 : K[X]) * a1 ^ 2) +
          Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) -
          Polynomial.C μ₄ *
            ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2) = h0 * s₂₃ ∧
      s₂₃ - Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) -
          Polynomial.C κ₇ * ((512 : K[X]) * a1) +
          (125829120 : K[X]) * a0 ^ 2 * a1 = h0 * s₂₄ ∧
      Polynomial.C μ₅ =
        s₂₄ - Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) -
          Polynomial.C μ₃ * ((3072 : K[X]) * a0) := by
  obtain ⟨s₂₄, hs₂₄⟩ : ∃ w : K[X],
      w = Polynomial.C μ * ((5505024 : K[X]) * a0 ^ 2) +
        Polynomial.C μ₃ * ((3072 : K[X]) * a0) +
        Polynomial.C μ₅ := ⟨_, rfl⟩
  obtain ⟨s₂₃, hs₂₃⟩ : ∃ w : K[X],
      w = Polynomial.C κ₃ * ((786432 : K[X]) * a0 * a1) +
        Polynomial.C κ₇ * ((512 : K[X]) * a1) -
        (125829120 : K[X]) * a0 ^ 2 * a1 + h0 * s₂₄ := ⟨_, rfl⟩
  obtain ⟨s₂₂, hs₂₂⟩ : ∃ w : K[X],
      w = (Polynomial.C κ₃ * ((98304 : K[X]) * a0) +
          Polynomial.C κ₇ * (64 : K[X]) -
          (15728640 : K[X]) * a0 ^ 2) * u * v -
        Polynomial.C μ * ((2752512 : K[X]) * a0 * a1 * u) +
        Polynomial.C μ₂ *
          ((81920 : K[X]) * a0 * a2 - (30720 : K[X]) * a0 * u ^ 2 +
            (40960 : K[X]) * a1 ^ 2) -
        Polynomial.C μ₃ * ((768 : K[X]) * a1 * u) +
        Polynomial.C μ₄ * ((32 : K[X]) * a2 - (12 : K[X]) * u ^ 2) +
        h0 * s₂₃ := ⟨_, rfl⟩
  obtain ⟨s₂₁, hs₂₁⟩ : ∃ w : K[X],
      w = ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
          a1 * v ^ 2 +
        ((62914560 : K[X]) * a0 - Polynomial.C κ₃ * (196608 : K[X])) *
          a1 ^ 2 * u + h0 * s₂₂ := ⟨_, rfl⟩
  obtain ⟨s₂₀, hs₂₀⟩ : ∃ w : K[X],
      w = ((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
          u * v ^ 3 +
        ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
          a1 * u ^ 2 * v -
        Polynomial.C μ *
          ((322560 : K[X]) * a0 * u ^ 4 -
            (1720320 : K[X]) * a0 * a2 * u ^ 2 +
            (1376256 : K[X]) * a0 * a2 ^ 2 -
            (860160 : K[X]) * a1 ^ 2 * u ^ 2 +
            (1376256 : K[X]) * a1 ^ 2 * a2) +
        Polynomial.C μ₂ *
          ((17920 : K[X]) * a1 * u ^ 3 - (61440 : K[X]) * a1 * a2 * u) -
        Polynomial.C μ₃ *
          ((90 : K[X]) * u ^ 4 - (480 : K[X]) * a2 * u ^ 2 +
            (384 : K[X]) * a2 ^ 2) + h0 * s₂₁ := ⟨_, rfl⟩
  obtain ⟨s₁₉, hs₁₉⟩ : ∃ w : K[X],
      w = (((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
          u ^ 2 - (2949120 : K[X]) * a1 ^ 2) * u * v ^ 2 -
        (5242880 : K[X]) * a1 ^ 3 *
          ((3 : K[X]) * u ^ 2 - (4 : K[X]) * a2) + h0 * s₂₀ := ⟨_, rfl⟩
  obtain ⟨s₁₈, hs₁₈⟩ : ∃ w : K[X],
      w = -(3932160 : K[X]) * a1 ^ 2 * u ^ 3 * v +
        Polynomial.C μ *
          ((209664 : K[X]) * a1 * u ^ 5 -
            (1290240 : K[X]) * a1 * a2 * u ^ 3 +
            (1720320 : K[X]) * a1 * a2 ^ 2 * u) +
        Polynomial.C μ₂ *
          ((1540 : K[X]) * u ^ 6 - (12320 : K[X]) * a2 * u ^ 4 +
            (26880 : K[X]) * a2 ^ 2 * u ^ 2 - (10240 : K[X]) * a2 ^ 3) +
        h0 * s₁₉ := ⟨_, rfl⟩
  obtain ⟨s₁₇, hs₁₇⟩ : ∃ w : K[X],
      w = -(30720 : K[X]) * a1 *
          ((33 : K[X]) * u ^ 4 - (72 : K[X]) * a2 * u ^ 2 +
            (16 : K[X]) * a2 ^ 2) * v ^ 2 + h0 * s₁₈ := ⟨_, rfl⟩
  refine ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hs₁₇, hs₁₈, hs₁₉, hs₂₀, hs₂₁, hs₂₂, hs₂₃, hs₂₄]
    linear_combination hcore
  · rw [hs₁₇]
    ring
  · rw [hs₁₈]
    ring
  · rw [hs₁₉]
    ring
  · rw [hs₂₀]
    ring
  · rw [hs₂₁]
    ring
  · rw [hs₂₂]
    ring
  · rw [hs₂₃]
    ring
  · rw [hs₂₄]
    ring

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 4000000 in
/-- Cleared nonsquare-core form of the eleventh defect relation:
cancelling `H¹¹` from `M₁₈ = 0` (parity kill) on `p₃ = H g`,
`M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₁₂ = κ₇ H¹²` exposes the
same core in `g` carried by `H²` against the explicit quotient — a
`q`-free constraint. -/
theorem alignedNonsquareEleventh_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12)
    (hM140 : alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
      0)
    (hM180 : alignedEleventhDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7
      κ = 0) :
    (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 - (104 : K[X]) * a2 * g ^ 2 +
            (48 : K[X]) * a2 ^ 2) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (30720 : K[X]) * H * a1 *
          ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
            (16 : K[X]) * a2 ^ 2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        ((1536 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) *
            (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                  g ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) -
              (2560 : K[X]) * a1 ^ 2 * g ^ 2) +
          (4096 : K[X]) * H * a1 *
            (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
              ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
              (1280 : K[X]) * a1 ^ 2 *
                ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2)) +
          (64 : K[X]) * H ^ 2 * g *
            ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
                (245760 : K[X]) * a0 ^ 2) *
                (g ^ 2 - (4 : K[X]) * a2) +
              ((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
                a1 ^ 2) +
          (512 : K[X]) * H ^ 3 * a1 *
            (Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
              (245760 : K[X]) * a0 ^ 2)) := by
  have hM18' := hM180
  simp only [alignedEleventhDefect410] at hM18'
  rw [hM140, hM12, hM100, hM60, hM4, hM20, hg] at hM18'
  apply mul_left_cancel₀ (pow_ne_zero 11 hH)
  linear_combination hM18'

set_option maxHeartbeats 4000000 in
/-- The consumed degree-`2` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` the row yields a `q`-free block
identity — the first aligned nonsquare row consuming NO letter.  The
block collapses at the core root to the perfect-cube product
`20480 g² (g f + 8 p₁)³`. -/
theorem alignedNonsquareEleventh_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 : K[X]} {κ₃ κ₇ : K}
    (hH : H ≠ 0)
    (hcore :
      (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
              (104 : K[X]) * a2 * g ^ 2 + (48 : K[X]) * a2 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (30720 : K[X]) * H * a1 *
            ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
              (16 : K[X]) * a2 ^ 2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          ((1536 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) *
              (((320 : K[X]) * a0 - Polynomial.C κ₃) *
                  (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
                (((640 : K[X]) * a0 - Polynomial.C κ₃ * (2 : K[X])) *
                    g ^ 2 - (1920 : K[X]) * a1 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2) -
                (2560 : K[X]) * a1 ^ 2 * g ^ 2) +
            (4096 : K[X]) * H * a1 *
              (((960 : K[X]) * a0 - Polynomial.C κ₃ * (3 : K[X])) *
                  (g ^ 2 - (4 : K[X]) * a2) ^ 2 +
                ((3840 : K[X]) * a0 - Polynomial.C κ₃ * (12 : K[X])) *
                  g ^ 2 * (g ^ 2 - (4 : K[X]) * a2) -
                (1280 : K[X]) * a1 ^ 2 *
                  ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2)) +
            (64 : K[X]) * H ^ 2 * g *
              ((Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                  Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2) *
                  (g ^ 2 - (4 : K[X]) * a2) +
                ((983040 : K[X]) * a0 -
                  Polynomial.C κ₃ * (3072 : K[X])) * a1 ^ 2) +
            (512 : K[X]) * H ^ 3 * a1 *
              (Polynomial.C κ₃ * ((1536 : K[X]) * a0) +
                Polynomial.C κ₇ - (245760 : K[X]) * a0 ^ 2)))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
          (104 : K[X]) * a2 * g ^ 2 + (48 : K[X]) * a2 ^ 2) * f ^ 3 +
        (30720 : K[X]) * a1 *
          ((33 : K[X]) * g ^ 4 - (72 : K[X]) * a2 * g ^ 2 +
            (16 : K[X]) * a2 ^ 2) * f ^ 2 +
        (3932160 : K[X]) * a1 ^ 2 * g ^ 3 * f +
        (5242880 : K[X]) * a1 ^ 3 *
          ((3 : K[X]) * g ^ 2 - (4 : K[X]) * a2) =
      H * ((((983040 : K[X]) * a0 - Polynomial.C κ₃ * (3072 : K[X])) *
            g ^ 2 - (2949120 : K[X]) * a1 ^ 2) * g * f ^ 2 +
        ((15728640 : K[X]) * a0 - Polynomial.C κ₃ * (49152 : K[X])) *
          a1 * g ^ 2 * f +
        ((62914560 : K[X]) * a0 - Polynomial.C κ₃ * (196608 : K[X])) *
          g * a1 ^ 2 +
        H * (((491520 : K[X]) * a0 - Polynomial.C κ₃ * (1536 : K[X])) *
            g * f ^ 3 +
          ((3932160 : K[X]) * a0 - Polynomial.C κ₃ * (12288 : K[X])) *
            a1 * f ^ 2 +
          (Polynomial.C κ₃ * ((1536 : K[X]) * a0) + Polynomial.C κ₇ -
            (245760 : K[X]) * a0 ^ 2) *
            ((64 : K[X]) * g * f + (512 : K[X]) * a1))) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing eleventh-row packets -/

/-- Source-facing squared weight-`33/2` integral of a normalized
aligned scale-two `(4,10)` source: the degree-`2` row is consumed into
`M₁₈² = κ₁₀ H³³` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedEleventhRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ : K,
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
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀,
    aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    hM14, hM16, hM18,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
half-integral form `M₁₈ = μ₅ h₀³³` with `μ₅² = κ₁₀` (honest residual),
the NEW μ-loaded octic divisibility carrying `s₁₇`, the explicit peels
producing `s₁₈` through `s₂₄`, and the constant pin
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`.  The constants `μ`, `κ₃`,
`μ₂`, `κ₅`, `μ₃`, `κ₇`, `μ₄`, `κ₉`, and `μ₅` are preserved, not
cleared. -/
theorem normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ μ₄ κ₉ μ₅ : K)
      (u v s₁₇ s₁₈ s₁₉ s₂₀ s₂₁ s₂₂ s₂₃ s₂₄ : K[X]),
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
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
              (104 : K[X]) * p.coeff 2 * u ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
            Polynomial.C μ *
              ((13923 : K[X]) * u ^ 8 -
                (148512 : K[X]) * p.coeff 2 * u ^ 6 +
                (524160 : K[X]) * p.coeff 2 ^ 2 * u ^ 4 -
                (645120 : K[X]) * p.coeff 2 ^ 3 * u ^ 2 +
                (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇ ∧
        s₁₇ + (30720 : K[X]) * p.coeff 1 *
            ((33 : K[X]) * u ^ 4 - (72 : K[X]) * p.coeff 2 * u ^ 2 +
              (16 : K[X]) * p.coeff 2 ^ 2) * v ^ 2 = h0 * s₁₈ ∧
        s₁₈ + (3932160 : K[X]) * p.coeff 1 ^ 2 * u ^ 3 * v -
            Polynomial.C μ *
              ((209664 : K[X]) * p.coeff 1 * u ^ 5 -
                (1290240 : K[X]) * p.coeff 1 * p.coeff 2 * u ^ 3 +
                (1720320 : K[X]) * p.coeff 1 * p.coeff 2 ^ 2 * u) -
            Polynomial.C μ₂ *
              ((1540 : K[X]) * u ^ 6 -
                (12320 : K[X]) * p.coeff 2 * u ^ 4 +
                (26880 : K[X]) * p.coeff 2 ^ 2 * u ^ 2 -
                (10240 : K[X]) * p.coeff 2 ^ 3) = h0 * s₁₉ ∧
        s₁₉ - (((983040 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (3072 : K[X])) * u ^ 2 -
              (2949120 : K[X]) * p.coeff 1 ^ 2) * u * v ^ 2 +
            (5242880 : K[X]) * p.coeff 1 ^ 3 *
              ((3 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) =
          h0 * s₂₀ ∧
        s₂₀ - ((491520 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (1536 : K[X])) * u * v ^ 3 -
            ((15728640 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (49152 : K[X])) *
              p.coeff 1 * u ^ 2 * v +
            Polynomial.C μ *
              ((322560 : K[X]) * p.coeff 0 * u ^ 4 -
                (1720320 : K[X]) * p.coeff 0 * p.coeff 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 0 * p.coeff 2 ^ 2 -
                (860160 : K[X]) * p.coeff 1 ^ 2 * u ^ 2 +
                (1376256 : K[X]) * p.coeff 1 ^ 2 * p.coeff 2) -
            Polynomial.C μ₂ *
              ((17920 : K[X]) * p.coeff 1 * u ^ 3 -
                (61440 : K[X]) * p.coeff 1 * p.coeff 2 * u) +
            Polynomial.C μ₃ *
              ((90 : K[X]) * u ^ 4 -
                (480 : K[X]) * p.coeff 2 * u ^ 2 +
                (384 : K[X]) * p.coeff 2 ^ 2) = h0 * s₂₁ ∧
        s₂₁ - ((3932160 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 * v ^ 2 -
            ((62914560 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (196608 : K[X])) *
              p.coeff 1 ^ 2 * u = h0 * s₂₂ ∧
        s₂₂ - (Polynomial.C κ₃ * ((98304 : K[X]) * p.coeff 0) +
              Polynomial.C κ₇ * (64 : K[X]) -
              (15728640 : K[X]) * p.coeff 0 ^ 2) * u * v +
            Polynomial.C μ *
              ((2752512 : K[X]) * p.coeff 0 * p.coeff 1 * u) -
            Polynomial.C μ₂ *
              ((81920 : K[X]) * p.coeff 0 * p.coeff 2 -
                (30720 : K[X]) * p.coeff 0 * u ^ 2 +
                (40960 : K[X]) * p.coeff 1 ^ 2) +
            Polynomial.C μ₃ * ((768 : K[X]) * p.coeff 1 * u) -
            Polynomial.C μ₄ *
              ((32 : K[X]) * p.coeff 2 - (12 : K[X]) * u ^ 2) =
          h0 * s₂₃ ∧
        s₂₃ - Polynomial.C κ₃ *
              ((786432 : K[X]) * p.coeff 0 * p.coeff 1) -
            Polynomial.C κ₇ * ((512 : K[X]) * p.coeff 1) +
            (125829120 : K[X]) * p.coeff 0 ^ 2 * p.coeff 1 =
          h0 * s₂₄ ∧
        Polynomial.C μ₅ =
          s₂₄ - Polynomial.C μ * ((5505024 : K[X]) * p.coeff 0 ^ 2) -
            Polynomial.C μ₃ * ((3072 : K[X]) * p.coeff 0) := by
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
  obtain ⟨κ₁₀, hM18rel⟩ :=
    alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
    thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
  have hcore11 :=
    alignedSquareEleventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM10form hM12form hM14form hM18form
  obtain ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hd1, hd2, hd3, hd4,
    hd5, hd6, hd7, hd8, hpin⟩ :=
    alignedSquareEleventh_solved_410 hh0 hcore11 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, u, v, s₁₇, s₁₈, s₁₉,
    s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hp3, hDform, hM4, hM6form, hM8form,
    hM10form, hM12form, hM14form, hM16, hM18form, hv, hd1, hd2, hd3,
    hd4, hd5, hd6, hd7, hd8, hpin⟩

/-- Exact nonsquare-chamber eleventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the parity
kill `M₁₈ ≡ 0` (with `κ₁₀ = 0` forced), and the `q`-free block
identity on the fifth face's divisibility `g² - 4 p₂ = H f` — the
first aligned nonsquare row consuming NO letter. -/
theorem normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet
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
        alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        ((1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
              (104 : K[X]) * p.coeff 2 * g ^ 2 +
              (48 : K[X]) * p.coeff 2 ^ 2) * f ^ 3 +
            (30720 : K[X]) * p.coeff 1 *
              ((33 : K[X]) * g ^ 4 - (72 : K[X]) * p.coeff 2 * g ^ 2 +
                (16 : K[X]) * p.coeff 2 ^ 2) * f ^ 2 +
            (3932160 : K[X]) * p.coeff 1 ^ 2 * g ^ 3 * f +
            (5242880 : K[X]) * p.coeff 1 ^ 3 *
              ((3 : K[X]) * g ^ 2 - (4 : K[X]) * p.coeff 2) =
          H * ((((983040 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (3072 : K[X])) * g ^ 2 -
                (2949120 : K[X]) * p.coeff 1 ^ 2) * g * f ^ 2 +
            ((15728640 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (49152 : K[X])) *
              p.coeff 1 * g ^ 2 * f +
            ((62914560 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (196608 : K[X])) *
              g * p.coeff 1 ^ 2 +
            H * (((491520 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (1536 : K[X])) * g * f ^ 3 +
              ((3932160 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (12288 : K[X])) * p.coeff 1 * f ^ 2 +
              (Polynomial.C κ₃ * ((1536 : K[X]) * p.coeff 0) +
                Polynomial.C κ₇ - (245760 : K[X]) * p.coeff 0 ^ 2) *
                ((64 : K[X]) * g * f +
                  (512 : K[X]) * p.coeff 1)))) := by
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
  have hcore11 :=
    alignedNonsquareEleventh_core_410 hH hg hD0 hM4 hM60 hM100 hM12form
      hM140 hM180
  have hblk := alignedNonsquareEleventh_solved_410 hH hcore11 hf
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, hD0, hM4, hM60, hM8form, hM100,
    hM12form, hM140, hM16, hM180, hf, hblk⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`2`
aligned row: the square chamber carries the half-integral form
`M₁₈ = μ₅ h₀³³` and the NEW μ-loaded octic divisibility carrying
`s₁₇` on the fifth face's divisibility; the nonsquare chamber carries
the parity kill `M₁₈ ≡ 0` and the fifth face's divisibility.  Neither
chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedEleventhRow_chamberDichotomy
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
      ∃ (κ μ μ₅ : K) (u v s₁₇ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
              (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C μ₅ * h0 ^ 33 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
                (104 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((13923 : K[X]) * u ^ 8 -
                  (148512 : K[X]) * p.coeff 2 * u ^ 6 +
                  (524160 : K[X]) * p.coeff 2 ^ 2 * u ^ 4 -
                  (645120 : K[X]) * p.coeff 2 ^ 3 * u ^ 2 +
                  (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
              (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, μ₄, κ₉, μ₅, u, v, s₁₇, s₁₈, s₁₉,
      s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hp3, hM2f, _hM4, _hM6f, _hM8, _hM10f,
      _hM12f, _hM14f, _hM16f, hM18f, hv, hd1, _hd2, _hd3, _hd4, _hd5,
      _hd6, _hd7, _hd8, _hpin⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, μ₅, u, v, s₁₇, hp3, hM2f, hM18f,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g, f, hg, _hM20, _hM4, _hM60, _hM8,
      _hM100, _hM12f, _hM140, _hM16f, hM180, hf, _hblk⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g, f, hg, hM180, hf⟩

/-- Extended root data of the consumed degree-`2` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order), and the NEW degree-`2` content splits by
chamber.  The square chamber gains the NEW value tie
`4096 u(a)⁵ v(a)³ = 7 μ u(a)⁸`, whose clash with the sixth face's
product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a factor-`255`
mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`, plus `s₁₇(a) = 0`, the
`s₁₇`/`s₁₈` ties, the μ₄-loaded tie on `s₂₂`, and the `μ₅` value tie —
the first aligned root tie seeing `μ₅`.  The nonsquare chamber's block
dies at `a` and collapses on the quadratic kill to the perfect-cube
product `g(a)² (g(a) f(a) + 8 p₁(a))³ = 0` — an independent
re-derivation of the eighth face's pin content as a product kill; no
new pin is claimed.  Both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedEleventhRow_rootData
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
      ((∃ (μ μ₂ μ₃ μ₄ κ₃ κ₇ μ₅ : K)
          (h0 u v s₁₇ s₁₈ s₂₂ s₂₄ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (1280 : K[X]) * u * ((39 : K[X]) * u ^ 4 -
                (104 : K[X]) * p.coeff 2 * u ^ 2 +
                (48 : K[X]) * p.coeff 2 ^ 2) * v ^ 3 -
              Polynomial.C μ *
                ((13923 : K[X]) * u ^ 8 -
                  (148512 : K[X]) * p.coeff 2 * u ^ 6 +
                  (524160 : K[X]) * p.coeff 2 ^ 2 * u ^ 4 -
                  (645120 : K[X]) * p.coeff 2 ^ 3 * u ^ 2 +
                  (143360 : K[X]) * p.coeff 2 ^ 4) = h0 * s₁₇ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (4096 : K) * u.eval a ^ 5 * v.eval a ^ 3 =
            (7 : K) * μ * u.eval a ^ 8 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₁₇.eval a =
            -(491520 : K) * (p.coeff 1).eval a * u.eval a ^ 4 *
              v.eval a ^ 2 ∧
          s₁₇.eval a = 0 ∧
          s₁₈.eval a =
            -(3932160 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 3 *
                v.eval a -
              (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 5 -
              (20 : K) * μ₂ * u.eval a ^ 6 ∧
          s₂₂.eval a =
            ((98304 : K) * κ₃ * (p.coeff 0).eval a + (64 : K) * κ₇ -
                (15728640 : K) * (p.coeff 0).eval a ^ 2) *
                u.eval a * v.eval a -
              (2752512 : K) * μ * (p.coeff 0).eval a *
                (p.coeff 1).eval a * u.eval a -
              (10240 : K) * μ₂ * (p.coeff 0).eval a * u.eval a ^ 2 +
              (40960 : K) * μ₂ * (p.coeff 1).eval a ^ 2 -
              (768 : K) * μ₃ * (p.coeff 1).eval a * u.eval a -
              (4 : K) * μ₄ * u.eval a ^ 2 ∧
          μ₅ = s₂₄.eval a -
            (5505024 : K) * μ * (p.coeff 0).eval a ^ 2 -
            (3072 : K) * μ₃ * (p.coeff 0).eval a) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (1280 : K) * g.eval a * ((39 : K) * g.eval a ^ 4 -
                  (104 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
                  (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
                (30720 : K) * (p.coeff 1).eval a *
                  ((33 : K) * g.eval a ^ 4 -
                    (72 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
                    (16 : K) * (p.coeff 2).eval a ^ 2) *
                  f.eval a ^ 2 +
                (3932160 : K) * (p.coeff 1).eval a ^ 2 *
                  g.eval a ^ 3 * f.eval a +
                (5242880 : K) * (p.coeff 1).eval a ^ 3 *
                  ((3 : K) * g.eval a ^ 2 -
                    (4 : K) * (p.coeff 2).eval a) = 0 ∧
            g.eval a ^ 2 * (g.eval a * f.eval a +
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
    obtain ⟨κ₁₀, hM18rel⟩ :=
      alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₅, _hμ₅2, hM18form⟩ :=
      thirtyThirdPower_squareChamber_form_410 hh0 hHsq hM18rel
    have hcore11 :=
      alignedSquareEleventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM10form hM12form hM14form hM18form
    obtain ⟨s₁₇, s₁₈, s₁₉, s₂₀, s₂₁, s₂₂, s₂₃, s₂₄, hd1, hd2, hd3, hd4,
      hd5, hd6, hd7, hd8, hpin⟩ :=
      alignedSquareEleventh_solved_410 hh0 hcore11 hv
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
        (1280 : K) * u.eval a * ((39 : K) * u.eval a ^ 4 -
              (104 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
              (48 : K) * (p.coeff 2).eval a ^ 2) * v.eval a ^ 3 -
          μ * ((13923 : K) * u.eval a ^ 8 -
            (148512 : K) * (p.coeff 2).eval a * u.eval a ^ 6 +
            (524160 : K) * (p.coeff 2).eval a ^ 2 * u.eval a ^ 4 -
            (645120 : K) * (p.coeff 2).eval a ^ 3 * u.eval a ^ 2 +
            (143360 : K) * (p.coeff 2).eval a ^ 4) = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd1
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hnewtie : (4096 : K) * u.eval a ^ 5 * v.eval a ^ 3 =
        (7 : K) * μ * u.eval a ^ 8 := by
      linear_combination (1 / 5 : K) * hd1a -
        ((32 / 5 : K) * ((1120 : K) * μ * (p.coeff 2).eval a ^ 3 -
          (4760 : K) * μ * (p.coeff 2).eval a ^ 2 * u.eval a ^ 2 +
          (2905 : K) * μ * (p.coeff 2).eval a * u.eval a ^ 4 -
          (434 : K) * μ * u.eval a ^ 6 -
          (480 : K) * (p.coeff 2).eval a * u.eval a * v.eval a ^ 3 +
          (920 : K) * u.eval a ^ 3 * v.eval a ^ 3)) * hkilla
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
        have h1785 : ((1785 : K) * μ) * u.eval a ^ 8 = 0 := by
          linear_combination hnewtie - (256 : K) * u.eval a ^ 5 * h16
        have h1785μ : (1785 : K) * μ = 0 :=
          (mul_eq_zero.mp h1785).resolve_right (pow_ne_zero 8 hu)
        have hμ0 : μ = 0 :=
          (mul_eq_zero.mp h1785μ).resolve_left (by norm_num)
        have h16v : (16 : K) * v.eval a ^ 3 = 0 := by
          rw [hμ0] at h16
          linear_combination h16
        have hv3 : v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp h16v).resolve_left (by norm_num)
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        exact Or.inr ⟨hv0, hμ0⟩
    have hs17raw : s₁₇.eval a =
        -(491520 : K) * (p.coeff 1).eval a * u.eval a ^ 4 *
          v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev +
        (30720 : K) * (p.coeff 1).eval a * v.eval a ^ 2 *
          ((4 : K) * (p.coeff 2).eval a - (17 : K) * u.eval a ^ 2) *
          hkilla
    have hs17kill : s₁₇.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs17raw, hu0]; ring
      · rw [hs17raw, hv0]; ring
    have hs18tie : s₁₈.eval a =
        -(3932160 : K) * (p.coeff 1).eval a ^ 2 * u.eval a ^ 3 *
            v.eval a -
          (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 5 -
          (20 : K) * μ₂ * u.eval a ^ 6 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (40 : K) * ((10752 : K) * μ * (p.coeff 1).eval a *
            (p.coeff 2).eval a * u.eval a -
          (5376 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 3 -
          (64 : K) * μ₂ * (p.coeff 2).eval a ^ 2 +
          (152 : K) * μ₂ * (p.coeff 2).eval a * u.eval a ^ 2 -
          (39 : K) * μ₂ * u.eval a ^ 4) * hkilla
    have hs22tie : s₂₂.eval a =
        ((98304 : K) * κ₃ * (p.coeff 0).eval a + (64 : K) * κ₇ -
            (15728640 : K) * (p.coeff 0).eval a ^ 2) *
            u.eval a * v.eval a -
          (2752512 : K) * μ * (p.coeff 0).eval a *
            (p.coeff 1).eval a * u.eval a -
          (10240 : K) * μ₂ * (p.coeff 0).eval a * u.eval a ^ 2 +
          (40960 : K) * μ₂ * (p.coeff 1).eval a ^ 2 -
          (768 : K) * μ₃ * (p.coeff 1).eval a * u.eval a -
          (4 : K) * μ₄ * u.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd7
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev -
        (8 : K) * ((2560 : K) * μ₂ * (p.coeff 0).eval a + μ₄) * hkilla
    have hμ₅tie : μ₅ = s₂₄.eval a -
        (5505024 : K) * μ * (p.coeff 0).eval a ^ 2 -
        (3072 : K) * μ₃ * (p.coeff 0).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hpin
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      linear_combination hev
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, μ₃, μ₄, κ₃, κ₇, μ₅, h0, u, v, s₁₇, s₁₈, s₂₂, s₂₄,
        hh0, hHsq, hroot, hp3, hv, hd1, hp3d, hkilla, hnewtie, hdich,
        hs17raw, hs17kill, hs18tie, hs22tie, hμ₅tie⟩⟩
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
    obtain ⟨κ₁₀, hM18rel⟩ :=
      alignedEleventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₁₀, hM180⟩ :=
      thirtyThirdPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM18rel
    have hcore11 :=
      alignedNonsquareEleventh_core_410 hH hg hD0 hM4 hM60 hM100
        hM12form hM140 hM180
    have hblk := alignedNonsquareEleventh_solved_410 hH hcore11 hf
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
    have hbtie : (1280 : K) * g.eval a * ((39 : K) * g.eval a ^ 4 -
            (104 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
            (48 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 3 +
        (30720 : K) * (p.coeff 1).eval a *
          ((33 : K) * g.eval a ^ 4 -
            (72 : K) * (p.coeff 2).eval a * g.eval a ^ 2 +
            (16 : K) * (p.coeff 2).eval a ^ 2) * f.eval a ^ 2 +
        (3932160 : K) * (p.coeff 1).eval a ^ 2 * g.eval a ^ 3 *
          f.eval a +
        (5242880 : K) * (p.coeff 1).eval a ^ 3 *
          ((3 : K) * g.eval a ^ 2 - (4 : K) * (p.coeff 2).eval a) =
        0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hblk
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hcube : (20480 : K) * (g.eval a ^ 2 *
        (g.eval a * f.eval a + (8 : K) * (p.coeff 1).eval a) ^ 3) =
        0 := by
      linear_combination hbtie -
        (1280 : K) * ((23 : K) * f.eval a ^ 3 * g.eval a ^ 3 -
          (12 : K) * f.eval a ^ 3 * g.eval a * (p.coeff 2).eval a +
          (408 : K) * f.eval a ^ 2 * g.eval a ^ 2 *
            (p.coeff 1).eval a -
          (96 : K) * f.eval a ^ 2 * (p.coeff 1).eval a *
            (p.coeff 2).eval a +
          (4096 : K) * (p.coeff 1).eval a ^ 3) * hkilla
    have hprod : g.eval a ^ 2 * (g.eval a * f.eval a +
        (8 : K) * (p.coeff 1).eval a) ^ 3 = 0 :=
      (mul_eq_zero.mp hcube).resolve_left (by norm_num)
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hbtie, hprod⟩⟩

#print axioms alignedEleventhCoefficientJacobianRow_410
#print axioms alignedEleventhDefect_weightedDerivative_identity_410
#print axioms alignedEleventhDefectRow_eq_zero_410
#print axioms thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410
#print axioms alignedEleventhDefectPowerRelation_410
#print axioms thirtyThirdPower_squareChamber_form_410
#print axioms thirtyThirdPower_nonsquareChamber_kill_410
#print axioms alignedSquareEleventh_core_410
#print axioms alignedSquareEleventh_solved_410
#print axioms alignedNonsquareEleventh_core_410
#print axioms alignedNonsquareEleventh_solved_410
#print axioms normalized410ScaleTwo_alignedEleventhRow_packet
#print axioms normalized410ScaleTwo_alignedEleventhRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedEleventhRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedEleventhRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedEleventhRow_rootData

end Max11DegreeRoutes
