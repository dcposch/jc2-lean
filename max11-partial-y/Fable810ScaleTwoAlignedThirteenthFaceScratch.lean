import Fable810ScaleTwoAlignedTwelfthFaceScratch

/-! # Thirteenth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedTwelfthFaceScratch` consumed the degree-`4`
aligned Keller row (the chambered `N₁₃² = κ₁₂ H⁹¹`).  This file
consumes the next unused aligned row, the degree-`3` Jacobian
coefficient (internal names `alignedFourteenth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9`/`8`/`7`/`6`/`5`/`4` rows
`2 H D' - 21 D H' = 0`, `H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`,
`H G' - 21 G H' = 0`, `2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`,
`2 H L' - 63 L H' = 0`, `H N₁₀' - 35 N₁₀ H' = 0`,
`2 H N₁₁' - 77 N₁₁ H' = 0`, `H N₁₂' - 42 N₁₂ H' = 0`,
`2 H N₁₃' - 91 N₁₃ H' = 0`, the degree-`3` row is the weighted
derivative of the weight-ninety-eight defect

`N₁₄ = -87960930222080 p₀ p₂ H⁴⁸ - 43980465111040 p₁² H⁴⁸
  + 70368744177664 p₀ q₄ H⁴⁷ + 52776558133248 p₁ q₃ H⁴⁷
  + 35184372088832 p₂ q₂ H⁴⁷ + 17592186044416 p₃ q₁ H⁴⁷
  + … + 198133678080 p₇¹⁴
  + κ (-2199023255552 p₀ p₄ H⁴⁷ - 2199023255552 p₁ p₃ H⁴⁷
       - 1099511627776 p₂² H⁴⁷ + … - 61641588736 p₇¹² H⁷)`

(the full three-hundred-sixty-two-term expression is the literal body
of `alignedFourteenthDefect810`; the defect is `q₀`-free — all five
weight-ninety-eight `q₀`-ansatz monomials `q₀ p₄ H⁴⁷`, `q₀ p₅ p₇ H⁴³`,
`q₀ p₆² H⁴³`, `q₀ p₆ p₇² H³⁹`, `q₀ p₇⁴ H³⁵` solve to zero — and `q₀`
enters the multiplier identity only through the `N₁₀`-row correction
`65536 p₄ H¹² (H N₁₀' - 35 N₁₀ H')`), via the exact multiplier
identity

`17592186044416 H⁴⁸ · row₃ = (H N₁₄' - 49 N₁₄ H')
  + (240518168576 p₀ p₅ H³⁶ + 240518168576 p₁ p₄ H³⁶
     + 240518168576 p₂ p₃ H³⁶ - … - 42178955 p₇¹¹) (2 H D' - 21 D H')
  + (25769803776 p₀ p₆ H³² + 25769803776 p₁ p₅ H³²
     + 25769803776 p₂ p₄ H³² + 12884901888 p₃² H³² - …
     + 16407040 p₇¹⁰) (H E' - 14 E H')
  + (1342177280 p₀ p₇ H²⁸ + 1342177280 p₁ p₆ H²⁸ + 1342177280 p₂ p₅ H²⁸
     + 1342177280 p₃ p₄ H²⁸ - … - 2291685 p₇⁹) (2 H F' - 35 F H')
  + (1073741824 p₀ H²⁸ + 536870912 p₁ p₇ H²⁴ + 536870912 p₂ p₆ H²⁴
     + 536870912 p₃ p₅ H²⁴ + … + 2162688 p₇⁸) (H G' - 21 G H')
  + (8388608 p₁ H²⁴ + 3145728 p₂ p₇ H²⁰ + 3145728 p₃ p₆ H²⁰
     + 3145728 p₄ p₅ H²⁰ - … - 27898 p₇⁷) (2 H I' - 49 I H')
  + (2097152 p₂ H²⁰ + 524288 p₃ p₇ H¹⁶ + 524288 p₄ p₆ H¹⁶
     + 262144 p₅² H¹⁶ - … + 9856 p₇⁶) (H J' - 28 J H')
  + (65536 p₃ H¹⁶ + 8192 p₄ p₇ H¹² + 8192 p₅ p₆ H¹² - 3584 p₅ p₇² H⁸
     - 3584 p₆² p₇ H⁸ + 2240 p₆ p₇³ H⁴ - 322 p₇⁵) (2 H L' - 63 L H')
  + 65536 p₄ H¹² (H N₁₀' - 35 N₁₀ H')
  + (128 p₅ H⁸ - 16 p₆ p₇ H⁴ + 3 p₇³) (2 H N₁₁' - 77 N₁₁ H')
  + (32 p₆ H⁴ - 4 p₇²) (H N₁₂' - 42 N₁₂ H')
  + p₇ (2 H N₁₃' - 91 N₁₃ H')`.

The row sees only `q₀, …, q₄`, so — as on the previous three faces —
no `N`- and no `C`-correction occurs at all: every correction is a
consumed tower row, and for the first time *four* integral-tower rows
(`N₁₀`, `N₁₁`, `N₁₂` and `N₁₃`) correct simultaneously (the
`N₁₀`-multiplier degenerates to the single monomial `65536 p₄ H¹²`
and the `N₁₃`-multiplier to the bare `p₇`).  On the aligned face every
right-hand correction vanishes, so `H N₁₄' = 49 N₁₄ H'` and the
weight-ninety-eight first integral

`N₁₄ = κ₁₃ H⁴⁹`

holds for a preserved constant `κ₁₃`.  The defect is unsquared, so —
exactly as for the degree-`13`, degree-`11`, degree-`9`, degree-`7`,
and degree-`5` rows — the integral is **chamber-free**: neither
chamber forces anything, and `κ₁₃` is preserved in both.

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: peeling `h₀⁵⁶` and
  consuming the previous factored quotient (`128 q₇ h₀²` solved,
  transported by the mate `-481036337152 p₀ p₅ h₀²⁸
  - 481036337152 p₁ p₄ h₀²⁸ - 481036337152 p₂ p₃ h₀²⁸
  + 721554505728 p₀ p₆ g₁ h₀²⁴ - 300647710720 p₀ g₁³ h₀²⁴
  + 721554505728 p₁ p₅ g₁ h₀²⁴ + 721554505728 p₂ p₄ g₁ h₀²⁴
  + 360777252864 p₃² g₁ h₀²⁴ + … + 15410397184 g₁¹¹`) leaves the
  cleared fourteenth row `alignedFourteenthSquareRow810` (with
  `q₁, …, q₆` re-tied at `h₀³⁸`) against `κ₁₃ h₀⁴²`, and the factored
  transport `2621440 (g₁² - 4 p₆) (46189 g₁¹² - 583440 p₆ g₁¹⁰
  + 2759328 p₆² g₁⁸ - 6040320 p₆³ g₁⁶ + 6057216 p₆⁴ g₁⁴
  - 2285568 p₆⁵ g₁² + 147456 p₆⁶) = h₀⁴ (κ₁₃ h₀³⁸ - co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): with
  `p₇ = H² g₂`, peeling `H²⁸` and consuming the previous factored
  quotient (same mate) leaves the cleared fourteenth row
  `alignedFourteenthNonsquareRow810` (with `q₁, …, q₆` at `H¹⁹`)
  against `κ₁₃ H²¹` and the transport `2621440 (g₂² - 4 p₆)
  (46189 g₂¹² - 583440 p₆ g₂¹⁰ + 2759328 p₆² g₂⁸ - 6040320 p₆³ g₂⁶
  + 6057216 p₆⁴ g₂⁴ - 2285568 p₆⁵ g₂² + 147456 p₆⁶)
  = H² (κ₁₃ H¹⁹ - co-factor)`.

At a root of the transport co-factor the honest root branch is, for
the first time on an unsquared row, a *split* one: the block factors
as `(g² - 4 p₆)` times an even dodecic with pure `p₆⁶` tail, so
`g(a)² = 4 p₆(a) ∨ 46189 g¹² - 583440 p₆ g¹⁰ + 2759328 p₆² g⁸
- 6040320 p₆³ g⁶ + 6057216 p₆⁴ g⁴ - 2285568 p₆⁵ g² + 147456 p₆⁶ = 0`
at the root.  Like the quartic through tridecic of the previous rows
it adds *no new* root information: the consumed degree-`13` row
already collapsed `g(a) = 0 ∧ p₆(a) = 0` at every core root, and that
collapse absorbs both branches identically
(`alignedFourteenth_rootQuattuordecic_absorbed_810`).  The
chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` — the
row re-ties `q₁, …, q₆` into the cleared fourteenth row (at `h₀³⁸`,
resp. `H¹⁹`) without killing anything new at the root.

No closure is claimed.  Both chambers remain open, nothing new is
forced (the unsquared integral forces neither `κ₁₃ = 0` nor
`N₁₄ ≡ 0` anywhere), the constants `κ`, `μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆`,
`κ₇`, `κ₈`, `κ₉`, `κ₁₀`, `κ₁₁`, `κ₁₂ = ν₅²`, and the new `κ₁₃` are
preserved where not previously forced (`κ₈ = 0`, `κ₁₀ = 0`, `κ₁₂ = 0`
remain forced in the nonsquare chamber only, by the consumed
degree-`8`, degree-`6` and degree-`4` rows), the zero branches
(`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`,
`κ₆ = 0`, `κ₇ = 0`, `κ₈ = 0` in the square chamber, `κ₉ = 0`,
`κ₁₀ = 0` in the square chamber, `κ₁₁ = 0`, `κ₁₂ = 0` in the square
chamber, `ν₅ = 0`, `κ₁₃ = 0`) are not excluded as polynomial
identities, the deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H`
from the degree-`13` face are still not re-cleared through the tower
here, the split root branch (`g² = 4 p₆` or the even dodecic) is
recorded but not excluded as an identity, and no individual vanishing
of `p₀`, `p₁`, `p₂`, `p₃`, `p₄`, `p₅`, `q₀`, `q₁`, `q₂`, `q₃`, `q₄`,
`q₅`, `q₆`, `q₇` is claimed.  The next unused Keller row on the
aligned face is the degree-`2` Jacobian coefficient
(weight-one-hundred-five defect, odd exponent, hence chambered).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal degree-`3` Keller coefficient on the aligned face -/

/-- The fourteenth row below the leading weighted-Wronskian row for
outer degrees `(8,10)`: the degree-`3` Jacobian coefficient. -/
theorem alignedFourteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
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
      ({(0, 3), (1, 2), (2, 1),
        (3, 0)} : Finset (ℕ × ℕ)) := by decide
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

/-! ## Aligned fourteenth defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-ninety-eight defect of the degree-`3` aligned `(8,10)` row.
On the aligned face it is a polynomial first integral of even weight
ninety-eight, hence chamber-free.  The defect is `q₀`-free. -/
def alignedFourteenthDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    K[X] :=
    -(87960930222080 : K[X]) * a0 * a2 * H ^ 48 -
    (43980465111040 : K[X]) * a1 ^ 2 * H ^ 48 +
    (70368744177664 : K[X]) * a0 * b4 * H ^ 47 +
    (52776558133248 : K[X]) * a1 * b3 * H ^ 47 +
    (35184372088832 : K[X]) * a2 * b2 * H ^ 47 +
    (17592186044416 : K[X]) * a3 * b1 * H ^ 47 +
    (32985348833280 : K[X]) * a0 * a3 * a7 * H ^ 44 +
    (43980465111040 : K[X]) * a0 * a4 * a6 * H ^ 44 +
    (65970697666560 : K[X]) * a0 * a5 ^ 2 * H ^ 44 +
    (32985348833280 : K[X]) * a1 * a2 * a7 * H ^ 44 +
    (43980465111040 : K[X]) * a1 * a3 * a6 * H ^ 44 +
    (131941395333120 : K[X]) * a1 * a4 * a5 * H ^ 44 +
    (21990232555520 : K[X]) * a2 ^ 2 * a6 * H ^ 44 +
    (131941395333120 : K[X]) * a2 * a3 * a5 * H ^ 44 +
    (65970697666560 : K[X]) * a2 * a4 ^ 2 * H ^ 44 +
    (65970697666560 : K[X]) * a3 ^ 2 * a4 * H ^ 44 -
    (61572651155456 : K[X]) * a0 * a5 * b7 * H ^ 43 -
    (52776558133248 : K[X]) * a0 * b6 * a6 * H ^ 43 -
    (43980465111040 : K[X]) * a0 * b5 * a7 * H ^ 43 -
    (61572651155456 : K[X]) * a1 * a4 * b7 * H ^ 43 -
    (52776558133248 : K[X]) * a1 * a5 * b6 * H ^ 43 -
    (43980465111040 : K[X]) * a1 * b5 * a6 * H ^ 43 -
    (35184372088832 : K[X]) * a1 * b4 * a7 * H ^ 43 -
    (61572651155456 : K[X]) * a2 * a3 * b7 * H ^ 43 -
    (52776558133248 : K[X]) * a2 * a4 * b6 * H ^ 43 -
    (43980465111040 : K[X]) * a2 * a5 * b5 * H ^ 43 -
    (35184372088832 : K[X]) * a2 * b4 * a6 * H ^ 43 -
    (26388279066624 : K[X]) * a2 * b3 * a7 * H ^ 43 -
    (26388279066624 : K[X]) * a3 ^ 2 * b6 * H ^ 43 -
    (43980465111040 : K[X]) * a3 * a4 * b5 * H ^ 43 -
    (35184372088832 : K[X]) * a3 * a5 * b4 * H ^ 43 -
    (26388279066624 : K[X]) * a3 * b3 * a6 * H ^ 43 -
    (17592186044416 : K[X]) * a3 * b2 * a7 * H ^ 43 -
    (17592186044416 : K[X]) * a4 ^ 2 * b4 * H ^ 43 -
    (26388279066624 : K[X]) * a4 * a5 * b3 * H ^ 43 -
    (17592186044416 : K[X]) * a4 * b2 * a6 * H ^ 43 -
    (8796093022208 : K[X]) * a4 * b1 * a7 * H ^ 43 -
    (8796093022208 : K[X]) * a5 ^ 2 * b2 * H ^ 43 -
    (8796093022208 : K[X]) * a5 * b1 * a6 * H ^ 43 -
    (27487790694400 : K[X]) * a0 * a4 * a7 ^ 2 * H ^ 40 -
    (49478023249920 : K[X]) * a0 * a5 * a6 * a7 * H ^ 40 +
    (10995116277760 : K[X]) * a0 * a6 ^ 3 * H ^ 40 -
    (27487790694400 : K[X]) * a1 * a3 * a7 ^ 2 * H ^ 40 -
    (49478023249920 : K[X]) * a1 * a4 * a6 * a7 * H ^ 40 -
    (90709709291520 : K[X]) * a1 * a5 ^ 2 * a7 * H ^ 40 -
    (32985348833280 : K[X]) * a1 * a5 * a6 ^ 2 * H ^ 40 -
    (13743895347200 : K[X]) * a2 ^ 2 * a7 ^ 2 * H ^ 40 -
    (49478023249920 : K[X]) * a2 * a3 * a6 * a7 * H ^ 40 -
    (181419418583040 : K[X]) * a2 * a4 * a5 * a7 * H ^ 40 -
    (32985348833280 : K[X]) * a2 * a4 * a6 ^ 2 * H ^ 40 -
    (98956046499840 : K[X]) * a2 * a5 ^ 2 * a6 * H ^ 40 -
    (90709709291520 : K[X]) * a3 ^ 2 * a5 * a7 * H ^ 40 -
    (16492674416640 : K[X]) * a3 ^ 2 * a6 ^ 2 * H ^ 40 -
    (90709709291520 : K[X]) * a3 * a4 ^ 2 * a7 * H ^ 40 -
    (197912092999680 : K[X]) * a3 * a4 * a5 * a6 * H ^ 40 -
    (54975581388800 : K[X]) * a3 * a5 ^ 3 * H ^ 40 -
    (32985348833280 : K[X]) * a4 ^ 3 * a6 * H ^ 40 -
    (82463372083200 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 40 +
    (92358976733184 : K[X]) * a0 * b7 * a6 * a7 * H ^ 39 +
    (39582418599936 : K[X]) * a0 * b6 * a7 ^ 2 * H ^ 39 +
    (92358976733184 : K[X]) * a1 * a5 * b7 * a7 * H ^ 39 +
    (46179488366592 : K[X]) * a1 * b7 * a6 ^ 2 * H ^ 39 +
    (79164837199872 : K[X]) * a1 * b6 * a6 * a7 * H ^ 39 +
    (32985348833280 : K[X]) * a1 * b5 * a7 ^ 2 * H ^ 39 +
    (92358976733184 : K[X]) * a2 * a4 * b7 * a7 * H ^ 39 +
    (92358976733184 : K[X]) * a2 * a5 * b7 * a6 * H ^ 39 +
    (79164837199872 : K[X]) * a2 * a5 * b6 * a7 * H ^ 39 +
    (39582418599936 : K[X]) * a2 * b6 * a6 ^ 2 * H ^ 39 +
    (65970697666560 : K[X]) * a2 * b5 * a6 * a7 * H ^ 39 +
    (26388279066624 : K[X]) * a2 * b4 * a7 ^ 2 * H ^ 39 +
    (46179488366592 : K[X]) * a3 ^ 2 * b7 * a7 * H ^ 39 +
    (92358976733184 : K[X]) * a3 * a4 * b7 * a6 * H ^ 39 +
    (79164837199872 : K[X]) * a3 * a4 * b6 * a7 * H ^ 39 +
    (46179488366592 : K[X]) * a3 * a5 ^ 2 * b7 * H ^ 39 +
    (79164837199872 : K[X]) * a3 * a5 * b6 * a6 * H ^ 39 +
    (65970697666560 : K[X]) * a3 * a5 * b5 * a7 * H ^ 39 +
    (32985348833280 : K[X]) * a3 * b5 * a6 ^ 2 * H ^ 39 +
    (52776558133248 : K[X]) * a3 * b4 * a6 * a7 * H ^ 39 +
    (19791209299968 : K[X]) * a3 * b3 * a7 ^ 2 * H ^ 39 +
    (46179488366592 : K[X]) * a4 ^ 2 * a5 * b7 * H ^ 39 +
    (39582418599936 : K[X]) * a4 ^ 2 * b6 * a6 * H ^ 39 +
    (32985348833280 : K[X]) * a4 ^ 2 * b5 * a7 * H ^ 39 +
    (39582418599936 : K[X]) * a4 * a5 ^ 2 * b6 * H ^ 39 +
    (65970697666560 : K[X]) * a4 * a5 * b5 * a6 * H ^ 39 +
    (52776558133248 : K[X]) * a4 * a5 * b4 * a7 * H ^ 39 +
    (26388279066624 : K[X]) * a4 * b4 * a6 ^ 2 * H ^ 39 +
    (39582418599936 : K[X]) * a4 * b3 * a6 * a7 * H ^ 39 +
    (13194139533312 : K[X]) * a4 * b2 * a7 ^ 2 * H ^ 39 +
    (10995116277760 : K[X]) * a5 ^ 3 * b5 * H ^ 39 +
    (26388279066624 : K[X]) * a5 ^ 2 * b4 * a6 * H ^ 39 +
    (19791209299968 : K[X]) * a5 ^ 2 * b3 * a7 * H ^ 39 +
    (19791209299968 : K[X]) * a5 * b3 * a6 ^ 2 * H ^ 39 +
    (26388279066624 : K[X]) * a5 * b2 * a6 * a7 * H ^ 39 +
    (6597069766656 : K[X]) * a5 * b1 * a7 ^ 2 * H ^ 39 +
    (4398046511104 : K[X]) * b2 * a6 ^ 3 * H ^ 39 +
    (6597069766656 : K[X]) * b1 * a6 ^ 2 * a7 * H ^ 39 +
    (23364622090240 : K[X]) * a0 * a5 * a7 ^ 3 * H ^ 36 -
    (53601191854080 : K[X]) * a0 * a6 ^ 2 * a7 ^ 2 * H ^ 36 +
    (23364622090240 : K[X]) * a1 * a4 * a7 ^ 3 * H ^ 36 +
    (57724360458240 : K[X]) * a1 * a5 * a6 * a7 ^ 2 * H ^ 36 -
    (34359738368000 : K[X]) * a1 * a6 ^ 3 * a7 * H ^ 36 +
    (23364622090240 : K[X]) * a2 * a3 * a7 ^ 3 * H ^ 36 +
    (57724360458240 : K[X]) * a2 * a4 * a6 * a7 ^ 2 * H ^ 36 +
    (111325552312320 : K[X]) * a2 * a5 ^ 2 * a7 ^ 2 * H ^ 36 +
    (61847529062400 : K[X]) * a2 * a5 * a6 ^ 2 * a7 * H ^ 36 -
    (6871947673600 : K[X]) * a2 * a6 ^ 4 * H ^ 36 +
    (28862180229120 : K[X]) * a3 ^ 2 * a6 * a7 ^ 2 * H ^ 36 +
    (222651104624640 : K[X]) * a3 * a4 * a5 * a7 ^ 2 * H ^ 36 +
    (61847529062400 : K[X]) * a3 * a4 * a6 ^ 2 * a7 * H ^ 36 +
    (226774273228800 : K[X]) * a3 * a5 ^ 2 * a6 * a7 * H ^ 36 +
    (27487790694400 : K[X]) * a3 * a5 * a6 ^ 3 * H ^ 36 +
    (37108517437440 : K[X]) * a4 ^ 3 * a7 ^ 2 * H ^ 36 +
    (226774273228800 : K[X]) * a4 ^ 2 * a5 * a6 * a7 * H ^ 36 +
    (13743895347200 : K[X]) * a4 ^ 2 * a6 ^ 3 * H ^ 36 +
    (130567005798400 : K[X]) * a4 * a5 ^ 3 * a7 * H ^ 36 +
    (123695058124800 : K[X]) * a4 * a5 ^ 2 * a6 ^ 2 * H ^ 36 +
    (34359738368000 : K[X]) * a5 ^ 4 * a6 * H ^ 36 -
    (38482906972160 : K[X]) * a0 * b7 * a7 ^ 3 * H ^ 35 -
    (115448720916480 : K[X]) * a1 * b7 * a6 * a7 ^ 2 * H ^ 35 -
    (32985348833280 : K[X]) * a1 * b6 * a7 ^ 3 * H ^ 35 -
    (115448720916480 : K[X]) * a2 * a5 * b7 * a7 ^ 2 * H ^ 35 -
    (115448720916480 : K[X]) * a2 * b7 * a6 ^ 2 * a7 * H ^ 35 -
    (98956046499840 : K[X]) * a2 * b6 * a6 * a7 ^ 2 * H ^ 35 -
    (27487790694400 : K[X]) * a2 * b5 * a7 ^ 3 * H ^ 35 -
    (115448720916480 : K[X]) * a3 * a4 * b7 * a7 ^ 2 * H ^ 35 -
    (230897441832960 : K[X]) * a3 * a5 * b7 * a6 * a7 * H ^ 35 -
    (98956046499840 : K[X]) * a3 * a5 * b6 * a7 ^ 2 * H ^ 35 -
    (38482906972160 : K[X]) * a3 * b7 * a6 ^ 3 * H ^ 35 -
    (98956046499840 : K[X]) * a3 * b6 * a6 ^ 2 * a7 * H ^ 35 -
    (82463372083200 : K[X]) * a3 * b5 * a6 * a7 ^ 2 * H ^ 35 -
    (21990232555520 : K[X]) * a3 * b4 * a7 ^ 3 * H ^ 35 -
    (115448720916480 : K[X]) * a4 ^ 2 * b7 * a6 * a7 * H ^ 35 -
    (49478023249920 : K[X]) * a4 ^ 2 * b6 * a7 ^ 2 * H ^ 35 -
    (115448720916480 : K[X]) * a4 * a5 ^ 2 * b7 * a7 * H ^ 35 -
    (115448720916480 : K[X]) * a4 * a5 * b7 * a6 ^ 2 * H ^ 35 -
    (197912092999680 : K[X]) * a4 * a5 * b6 * a6 * a7 * H ^ 35 -
    (82463372083200 : K[X]) * a4 * a5 * b5 * a7 ^ 2 * H ^ 35 -
    (32985348833280 : K[X]) * a4 * b6 * a6 ^ 3 * H ^ 35 -
    (82463372083200 : K[X]) * a4 * b5 * a6 ^ 2 * a7 * H ^ 35 -
    (65970697666560 : K[X]) * a4 * b4 * a6 * a7 ^ 2 * H ^ 35 -
    (16492674416640 : K[X]) * a4 * b3 * a7 ^ 3 * H ^ 35 -
    (38482906972160 : K[X]) * a5 ^ 3 * b7 * a6 * H ^ 35 -
    (32985348833280 : K[X]) * a5 ^ 3 * b6 * a7 * H ^ 35 -
    (49478023249920 : K[X]) * a5 ^ 2 * b6 * a6 ^ 2 * H ^ 35 -
    (82463372083200 : K[X]) * a5 ^ 2 * b5 * a6 * a7 * H ^ 35 -
    (32985348833280 : K[X]) * a5 ^ 2 * b4 * a7 ^ 2 * H ^ 35 -
    (27487790694400 : K[X]) * a5 * b5 * a6 ^ 3 * H ^ 35 -
    (65970697666560 : K[X]) * a5 * b4 * a6 ^ 2 * a7 * H ^ 35 -
    (49478023249920 : K[X]) * a5 * b3 * a6 * a7 ^ 2 * H ^ 35 -
    (10995116277760 : K[X]) * a5 * b2 * a7 ^ 3 * H ^ 35 -
    (5497558138880 : K[X]) * b4 * a6 ^ 4 * H ^ 35 -
    (16492674416640 : K[X]) * b3 * a6 ^ 3 * a7 * H ^ 35 -
    (16492674416640 : K[X]) * b2 * a6 ^ 2 * a7 ^ 2 * H ^ 35 -
    (5497558138880 : K[X]) * b1 * a6 * a7 ^ 3 * H ^ 35 +
    (27487790694400 : K[X]) * a0 * a6 * a7 ^ 4 * H ^ 32 -
    (20615843020800 : K[X]) * a1 * a5 * a7 ^ 4 * H ^ 32 +
    (63565515980800 : K[X]) * a1 * a6 ^ 2 * a7 ^ 3 * H ^ 32 -
    (20615843020800 : K[X]) * a2 * a4 * a7 ^ 4 * H ^ 32 -
    (65283502899200 : K[X]) * a2 * a5 * a6 * a7 ^ 3 * H ^ 32 +
    (65283502899200 : K[X]) * a2 * a6 ^ 3 * a7 ^ 2 * H ^ 32 -
    (10307921510400 : K[X]) * a3 ^ 2 * a7 ^ 4 * H ^ 32 -
    (65283502899200 : K[X]) * a3 * a4 * a6 * a7 ^ 3 * H ^ 32 -
    (128849018880000 : K[X]) * a3 * a5 ^ 2 * a7 ^ 3 * H ^ 32 -
    (92771293593600 : K[X]) * a3 * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 32 +
    (30064771072000 : K[X]) * a3 * a6 ^ 4 * a7 * H ^ 32 -
    (128849018880000 : K[X]) * a4 ^ 2 * a5 * a7 ^ 3 * H ^ 32 -
    (46385646796800 : K[X]) * a4 ^ 2 * a6 ^ 2 * a7 ^ 2 * H ^ 32 -
    (381393095884800 : K[X]) * a4 * a5 ^ 2 * a6 * a7 ^ 2 * H ^ 32 -
    (72155450572800 : K[X]) * a4 * a5 * a6 ^ 3 * a7 * H ^ 32 +
    (4810363371520 : K[X]) * a4 * a6 ^ 5 * H ^ 32 -
    (55834574848000 : K[X]) * a5 ^ 4 * a7 ^ 2 * H ^ 32 -
    (132284992716800 : K[X]) * a5 ^ 3 * a6 ^ 2 * a7 * H ^ 32 -
    (12025908428800 : K[X]) * a5 ^ 2 * a6 ^ 4 * H ^ 32 +
    (33672543600640 : K[X]) * a1 * b7 * a7 ^ 4 * H ^ 31 +
    (134690174402560 : K[X]) * a2 * b7 * a6 * a7 ^ 3 * H ^ 31 +
    (28862180229120 : K[X]) * a2 * b6 * a7 ^ 4 * H ^ 31 +
    (134690174402560 : K[X]) * a3 * a5 * b7 * a7 ^ 3 * H ^ 31 +
    (202035261603840 : K[X]) * a3 * b7 * a6 ^ 2 * a7 ^ 2 * H ^ 31 +
    (115448720916480 : K[X]) * a3 * b6 * a6 * a7 ^ 3 * H ^ 31 +
    (24051816857600 : K[X]) * a3 * b5 * a7 ^ 4 * H ^ 31 +
    (67345087201280 : K[X]) * a4 ^ 2 * b7 * a7 ^ 3 * H ^ 31 +
    (404070523207680 : K[X]) * a4 * a5 * b7 * a6 * a7 ^ 2 * H ^ 31 +
    (115448720916480 : K[X]) * a4 * a5 * b6 * a7 ^ 3 * H ^ 31 +
    (134690174402560 : K[X]) * a4 * b7 * a6 ^ 3 * a7 * H ^ 31 +
    (173173081374720 : K[X]) * a4 * b6 * a6 ^ 2 * a7 ^ 2 * H ^ 31 +
    (96207267430400 : K[X]) * a4 * b5 * a6 * a7 ^ 3 * H ^ 31 +
    (19241453486080 : K[X]) * a4 * b4 * a7 ^ 4 * H ^ 31 +
    (67345087201280 : K[X]) * a5 ^ 3 * b7 * a7 ^ 2 * H ^ 31 +
    (202035261603840 : K[X]) * a5 ^ 2 * b7 * a6 ^ 2 * a7 * H ^ 31 +
    (173173081374720 : K[X]) * a5 ^ 2 * b6 * a6 * a7 ^ 2 * H ^ 31 +
    (48103633715200 : K[X]) * a5 ^ 2 * b5 * a7 ^ 3 * H ^ 31 +
    (33672543600640 : K[X]) * a5 * b7 * a6 ^ 4 * H ^ 31 +
    (115448720916480 : K[X]) * a5 * b6 * a6 ^ 3 * a7 * H ^ 31 +
    (144310901145600 : K[X]) * a5 * b5 * a6 ^ 2 * a7 ^ 2 * H ^ 31 +
    (76965813944320 : K[X]) * a5 * b4 * a6 * a7 ^ 3 * H ^ 31 +
    (14431090114560 : K[X]) * a5 * b3 * a7 ^ 4 * H ^ 31 +
    (5772436045824 : K[X]) * b6 * a6 ^ 5 * H ^ 31 +
    (24051816857600 : K[X]) * b5 * a6 ^ 4 * a7 * H ^ 31 +
    (38482906972160 : K[X]) * b4 * a6 ^ 3 * a7 ^ 2 * H ^ 31 +
    (28862180229120 : K[X]) * b3 * a6 ^ 2 * a7 ^ 3 * H ^ 31 +
    (9620726743040 : K[X]) * b2 * a6 * a7 ^ 4 * H ^ 31 +
    (962072674304 : K[X]) * b1 * a7 ^ 5 * H ^ 31 -
    (3006477107200 : K[X]) * a0 * a7 ^ 6 * H ^ 28 -
    (24653112279040 : K[X]) * a1 * a6 * a7 ^ 5 * H ^ 28 +
    (18640158064640 : K[X]) * a2 * a5 * a7 ^ 5 * H ^ 28 -
    (72155450572800 : K[X]) * a2 * a6 ^ 2 * a7 ^ 4 * H ^ 28 +
    (18640158064640 : K[X]) * a3 * a4 * a7 ^ 5 * H ^ 28 +
    (72155450572800 : K[X]) * a3 * a5 * a6 * a7 ^ 4 * H ^ 28 -
    (102220221644800 : K[X]) * a3 * a6 ^ 3 * a7 ^ 3 * H ^ 28 +
    (36077725286400 : K[X]) * a4 ^ 2 * a6 * a7 ^ 4 * H ^ 28 +
    (144310901145600 : K[X]) * a4 * a5 ^ 2 * a7 ^ 4 * H ^ 28 +
    (126272038502400 : K[X]) * a4 * a5 * a6 ^ 2 * a7 ^ 3 * H ^ 28 -
    (75161927680000 : K[X]) * a4 * a6 ^ 4 * a7 ^ 2 * H ^ 28 +
    (186401580646400 : K[X]) * a5 ^ 3 * a6 * a7 ^ 3 * H ^ 28 +
    (66142496358400 : K[X]) * a5 ^ 2 * a6 ^ 3 * a7 ^ 2 * H ^ 28 -
    (27058293964800 : K[X]) * a5 * a6 ^ 5 * a7 * H ^ 28 -
    (1546188226560 : K[X]) * a6 ^ 7 * H ^ 28 -
    (30305289240576 : K[X]) * a2 * b7 * a7 ^ 5 * H ^ 27 -
    (151526446202880 : K[X]) * a3 * b7 * a6 * a7 ^ 4 * H ^ 27 -
    (25975962206208 : K[X]) * a3 * b6 * a7 ^ 5 * H ^ 27 -
    (151526446202880 : K[X]) * a4 * a5 * b7 * a7 ^ 4 * H ^ 27 -
    (303052892405760 : K[X]) * a4 * b7 * a6 ^ 2 * a7 ^ 3 * H ^ 27 -
    (129879811031040 : K[X]) * a4 * b6 * a6 * a7 ^ 4 * H ^ 27 -
    (21646635171840 : K[X]) * a4 * b5 * a7 ^ 5 * H ^ 27 -
    (303052892405760 : K[X]) * a5 ^ 2 * b7 * a6 * a7 ^ 3 * H ^ 27 -
    (64939905515520 : K[X]) * a5 ^ 2 * b6 * a7 ^ 4 * H ^ 27 -
    (303052892405760 : K[X]) * a5 * b7 * a6 ^ 3 * a7 ^ 2 * H ^ 27 -
    (259759622062080 : K[X]) * a5 * b6 * a6 ^ 2 * a7 ^ 3 * H ^ 27 -
    (108233175859200 : K[X]) * a5 * b5 * a6 * a7 ^ 4 * H ^ 27 -
    (17317308137472 : K[X]) * a5 * b4 * a7 ^ 5 * H ^ 27 -
    (30305289240576 : K[X]) * b7 * a6 ^ 5 * a7 * H ^ 27 -
    (64939905515520 : K[X]) * b6 * a6 ^ 4 * a7 ^ 2 * H ^ 27 -
    (72155450572800 : K[X]) * b5 * a6 ^ 3 * a7 ^ 3 * H ^ 27 -
    (43293270343680 : K[X]) * b4 * a6 ^ 2 * a7 ^ 4 * H ^ 27 -
    (12987981103104 : K[X]) * b3 * a6 * a7 ^ 5 * H ^ 27 -
    (1443109011456 : K[X]) * b2 * a7 ^ 6 * H ^ 27 +
    (2383706849280 : K[X]) * a1 * a7 ^ 7 * H ^ 24 +
    (22548578304000 : K[X]) * a2 * a6 * a7 ^ 6 * H ^ 24 -
    (17136919511040 : K[X]) * a3 * a5 * a7 ^ 6 * H ^ 24 +
    (79821967196160 : K[X]) * a3 * a6 ^ 2 * a7 ^ 5 * H ^ 24 -
    (8568459755520 : K[X]) * a4 ^ 2 * a7 ^ 6 * H ^ 24 -
    (78469052497920 : K[X]) * a4 * a5 * a6 * a7 ^ 5 * H ^ 24 +
    (144310901145600 : K[X]) * a4 * a6 ^ 3 * a7 ^ 4 * H ^ 24 -
    (52763673231360 : K[X]) * a5 ^ 3 * a7 ^ 5 * H ^ 24 -
    (81174881894400 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 ^ 4 * H ^ 24 +
    (146565758976000 : K[X]) * a5 * a6 ^ 4 * a7 ^ 3 * H ^ 24 +
    (33822867456000 : K[X]) * a6 ^ 6 * a7 ^ 2 * H ^ 24 +
    (27779848470528 : K[X]) * a3 * b7 * a7 ^ 6 * H ^ 23 +
    (166679090823168 : K[X]) * a4 * b7 * a6 * a7 ^ 5 * H ^ 23 +
    (23811298689024 : K[X]) * a4 * b6 * a7 ^ 6 * H ^ 23 +
    (83339545411584 : K[X]) * a5 ^ 2 * b7 * a7 ^ 5 * H ^ 23 +
    (416697727057920 : K[X]) * a5 * b7 * a6 ^ 2 * a7 ^ 4 * H ^ 23 +
    (142867792134144 : K[X]) * a5 * b6 * a6 * a7 ^ 5 * H ^ 23 +
    (19842748907520 : K[X]) * a5 * b5 * a7 ^ 6 * H ^ 23 +
    (138899242352640 : K[X]) * b7 * a6 ^ 4 * a7 ^ 3 * H ^ 23 +
    (119056493445120 : K[X]) * b6 * a6 ^ 3 * a7 ^ 4 * H ^ 23 +
    (59528246722560 : K[X]) * b5 * a6 ^ 2 * a7 ^ 5 * H ^ 23 +
    (15874199126016 : K[X]) * b4 * a6 * a7 ^ 6 * H ^ 23 +
    (1700807049216 : K[X]) * b3 * a7 ^ 7 * H ^ 23 -
    (1948841410560 : K[X]) * a2 * a7 ^ 8 * H ^ 20 -
    (20905753313280 : K[X]) * a3 * a6 * a7 ^ 7 * H ^ 20 +
    (15945066086400 : K[X]) * a4 * a5 * a7 ^ 7 * H ^ 20 -
    (86812026470400 : K[X]) * a4 * a6 ^ 2 * a7 ^ 6 * H ^ 20 +
    (42165841428480 : K[X]) * a5 ^ 2 * a6 * a7 ^ 6 * H ^ 20 -
    (190986458234880 : K[X]) * a5 * a6 ^ 3 * a7 ^ 5 * H ^ 20 -
    (114095806218240 : K[X]) * a6 ^ 5 * a7 ^ 4 * H ^ 20 -
    (25795573579776 : K[X]) * a4 * b7 * a7 ^ 7 * H ^ 19 -
    (180569015058432 : K[X]) * a5 * b7 * a6 * a7 ^ 6 * H ^ 19 -
    (22110491639808 : K[X]) * a5 * b6 * a7 ^ 7 * H ^ 19 -
    (180569015058432 : K[X]) * b7 * a6 ^ 3 * a7 ^ 5 * H ^ 19 -
    (77386720739328 : K[X]) * b6 * a6 ^ 2 * a7 ^ 6 * H ^ 19 -
    (18425409699840 : K[X]) * b5 * a6 * a7 ^ 7 * H ^ 19 -
    (1842540969984 : K[X]) * b4 * a7 ^ 8 * H ^ 19 +
    (1631416483840 : K[X]) * a3 * a7 ^ 9 * H ^ 16 +
    (19576997806080 : K[X]) * a4 * a6 * a7 ^ 8 * H ^ 16 -
    (7485322690560 : K[X]) * a5 ^ 2 * a7 ^ 8 * H ^ 16 +
    (93278636605440 : K[X]) * a5 * a6 ^ 2 * a7 ^ 7 * H ^ 16 +
    (141069543014400 : K[X]) * a6 ^ 4 * a7 ^ 6 * H ^ 16 +
    (24183350231040 : K[X]) * a5 * b7 * a7 ^ 8 * H ^ 15 +
    (96733400924160 : K[X]) * b7 * a6 ^ 2 * a7 ^ 7 * H ^ 15 +
    (20728585912320 : K[X]) * b6 * a6 * a7 ^ 8 * H ^ 15 +
    (1919313510400 : K[X]) * b5 * a7 ^ 9 * H ^ 15 -
    (1391502295040 : K[X]) * a4 * a7 ^ 10 * H ^ 12 -
    (18473392537600 : K[X]) * a5 * a6 * a7 ^ 9 * H ^ 12 -
    (82050652569600 : K[X]) * a6 ^ 3 * a7 ^ 8 * H ^ 12 -
    (22839830773760 : K[X]) * b7 * a6 * a7 ^ 9 * H ^ 11 -
    (1957699780608 : K[X]) * b6 * a7 ^ 10 * H ^ 11 +
    (1205023539200 : K[X]) * a5 * a7 ^ 11 * H ^ 8 +
    (24267320197120 : K[X]) * a6 ^ 2 * a7 ^ 10 * H ^ 8 +
    (1972530839552 : K[X]) * b7 * a7 ^ 11 * H ^ 7 -
    (3522376499200 : K[X]) * a6 * a7 ^ 12 * H ^ 4 +
    (198133678080 : K[X]) * a7 ^ 14 +
    Polynomial.C κ *
      (-(2199023255552 : K[X]) * a0 * a4 * H ^ 47 -
        (2199023255552 : K[X]) * a1 * a3 * H ^ 47 -
        (1099511627776 : K[X]) * a2 ^ 2 * H ^ 47 +
        (3298534883328 : K[X]) * a0 * a5 * a7 * H ^ 43 +
        (1649267441664 : K[X]) * a0 * a6 ^ 2 * H ^ 43 +
        (3298534883328 : K[X]) * a1 * a4 * a7 * H ^ 43 +
        (3298534883328 : K[X]) * a1 * a5 * a6 * H ^ 43 +
        (3298534883328 : K[X]) * a2 * a3 * a7 * H ^ 43 +
        (3298534883328 : K[X]) * a2 * a4 * a6 * H ^ 43 +
        (1649267441664 : K[X]) * a2 * a5 ^ 2 * H ^ 43 +
        (1649267441664 : K[X]) * a3 ^ 2 * a6 * H ^ 43 +
        (3298534883328 : K[X]) * a3 * a4 * a5 * H ^ 43 +
        (549755813888 : K[X]) * a4 ^ 3 * H ^ 43 -
        (4123168604160 : K[X]) * a0 * a6 * a7 ^ 2 * H ^ 39 -
        (4123168604160 : K[X]) * a1 * a5 * a7 ^ 2 * H ^ 39 -
        (4123168604160 : K[X]) * a1 * a6 ^ 2 * a7 * H ^ 39 -
        (4123168604160 : K[X]) * a2 * a4 * a7 ^ 2 * H ^ 39 -
        (8246337208320 : K[X]) * a2 * a5 * a6 * a7 * H ^ 39 -
        (1374389534720 : K[X]) * a2 * a6 ^ 3 * H ^ 39 -
        (2061584302080 : K[X]) * a3 ^ 2 * a7 ^ 2 * H ^ 39 -
        (8246337208320 : K[X]) * a3 * a4 * a6 * a7 * H ^ 39 -
        (4123168604160 : K[X]) * a3 * a5 ^ 2 * a7 * H ^ 39 -
        (4123168604160 : K[X]) * a3 * a5 * a6 ^ 2 * H ^ 39 -
        (4123168604160 : K[X]) * a4 ^ 2 * a5 * a7 * H ^ 39 -
        (2061584302080 : K[X]) * a4 ^ 2 * a6 ^ 2 * H ^ 39 -
        (4123168604160 : K[X]) * a4 * a5 ^ 2 * a6 * H ^ 39 -
        (343597383680 : K[X]) * a5 ^ 4 * H ^ 39 +
        (1202590842880 : K[X]) * a0 * a7 ^ 4 * H ^ 35 +
        (4810363371520 : K[X]) * a1 * a6 * a7 ^ 3 * H ^ 35 +
        (4810363371520 : K[X]) * a2 * a5 * a7 ^ 3 * H ^ 35 +
        (7215545057280 : K[X]) * a2 * a6 ^ 2 * a7 ^ 2 * H ^ 35 +
        (4810363371520 : K[X]) * a3 * a4 * a7 ^ 3 * H ^ 35 +
        (14431090114560 : K[X]) * a3 * a5 * a6 * a7 ^ 2 * H ^ 35 +
        (4810363371520 : K[X]) * a3 * a6 ^ 3 * a7 * H ^ 35 +
        (7215545057280 : K[X]) * a4 ^ 2 * a6 * a7 ^ 2 * H ^ 35 +
        (7215545057280 : K[X]) * a4 * a5 ^ 2 * a7 ^ 2 * H ^ 35 +
        (14431090114560 : K[X]) * a4 * a5 * a6 ^ 2 * a7 * H ^ 35 +
        (1202590842880 : K[X]) * a4 * a6 ^ 4 * H ^ 35 +
        (4810363371520 : K[X]) * a5 ^ 3 * a6 * a7 * H ^ 35 +
        (2405181685760 : K[X]) * a5 ^ 2 * a6 ^ 3 * H ^ 35 -
        (1082331758592 : K[X]) * a1 * a7 ^ 5 * H ^ 31 -
        (5411658792960 : K[X]) * a2 * a6 * a7 ^ 4 * H ^ 31 -
        (5411658792960 : K[X]) * a3 * a5 * a7 ^ 4 * H ^ 31 -
        (10823317585920 : K[X]) * a3 * a6 ^ 2 * a7 ^ 3 * H ^ 31 -
        (2705829396480 : K[X]) * a4 ^ 2 * a7 ^ 4 * H ^ 31 -
        (21646635171840 : K[X]) * a4 * a5 * a6 * a7 ^ 3 * H ^ 31 -
        (10823317585920 : K[X]) * a4 * a6 ^ 3 * a7 ^ 2 * H ^ 31 -
        (3607772528640 : K[X]) * a5 ^ 3 * a7 ^ 3 * H ^ 31 -
        (16234976378880 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 ^ 2 * H ^ 31 -
        (5411658792960 : K[X]) * a5 * a6 ^ 4 * a7 * H ^ 31 -
        (180388626432 : K[X]) * a6 ^ 6 * H ^ 31 +
        (992137445376 : K[X]) * a2 * a7 ^ 6 * H ^ 27 +
        (5952824672256 : K[X]) * a3 * a6 * a7 ^ 5 * H ^ 27 +
        (5952824672256 : K[X]) * a4 * a5 * a7 ^ 5 * H ^ 27 +
        (14882061680640 : K[X]) * a4 * a6 ^ 2 * a7 ^ 4 * H ^ 27 +
        (14882061680640 : K[X]) * a5 ^ 2 * a6 * a7 ^ 4 * H ^ 27 +
        (19842748907520 : K[X]) * a5 * a6 ^ 3 * a7 ^ 3 * H ^ 27 +
        (2976412336128 : K[X]) * a6 ^ 5 * a7 ^ 2 * H ^ 27 -
        (921270484992 : K[X]) * a3 * a7 ^ 7 * H ^ 23 -
        (6448893394944 : K[X]) * a4 * a6 * a7 ^ 6 * H ^ 23 -
        (3224446697472 : K[X]) * a5 ^ 2 * a7 ^ 6 * H ^ 23 -
        (19346680184832 : K[X]) * a5 * a6 ^ 2 * a7 ^ 5 * H ^ 23 -
        (8061116743680 : K[X]) * a6 ^ 4 * a7 ^ 4 * H ^ 23 +
        (863691079680 : K[X]) * a4 * a7 ^ 8 * H ^ 19 +
        (6909528637440 : K[X]) * a5 * a6 * a7 ^ 7 * H ^ 19 +
        (8061116743680 : K[X]) * a6 ^ 3 * a7 ^ 6 * H ^ 19 -
        (815708241920 : K[X]) * a5 * a7 ^ 9 * H ^ 15 -
        (3670687088640 : K[X]) * a6 ^ 2 * a7 ^ 8 * H ^ 15 +
        (774922829824 : K[X]) * a6 * a7 ^ 10 * H ^ 11 -
        (61641588736 : K[X]) * a7 ^ 12 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`3` Jacobian expression with the
weighted derivative of `N₁₄`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` through
degree-`4` rows.  The row sees only `q₀, …, q₄`, so no `N`- and no
`C`-correction occurs at all; for the first time four integral-tower
rows (`N₁₀`, `N₁₁`, `N₁₂` and `N₁₃`) correct simultaneously, and `q₀`
couples only through the `N₁₀`-row correction. -/
theorem alignedFourteenthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    (17592186044416 : K[X]) * H ^ 48 *
        (a3.derivative * b1 +
          a2.derivative * (b2 * (2 : K[X])) +
          a1.derivative * (b3 * (3 : K[X])) +
          a0.derivative * (b4 * (4 : K[X])) -
        ((a4 * (4 : K[X])) * b0.derivative +
          (a3 * (3 : K[X])) * b1.derivative +
          (a2 * (2 : K[X])) * b2.derivative +
          a1 * b3.derivative)) =
      (H *
          (alignedFourteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ).derivative -
        (49 : K[X]) *
          alignedFourteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ * H.derivative) +
        ((240518168576 : K[X]) * a0 * a5 * H ^ 36 +
            (240518168576 : K[X]) * a1 * a4 * H ^ 36 +
            (240518168576 : K[X]) * a2 * a3 * H ^ 36 -
            (30064771072 : K[X]) * a0 * a6 * a7 * H ^ 32 -
            (30064771072 : K[X]) * a1 * a5 * a7 * H ^ 32 -
            (15032385536 : K[X]) * a1 * a6 ^ 2 * H ^ 32 -
            (30064771072 : K[X]) * a2 * a4 * a7 * H ^ 32 -
            (30064771072 : K[X]) * a2 * a5 * a6 * H ^ 32 -
            (15032385536 : K[X]) * a3 ^ 2 * a7 * H ^ 32 -
            (30064771072 : K[X]) * a3 * a4 * a6 * H ^ 32 -
            (15032385536 : K[X]) * a3 * a5 ^ 2 * H ^ 32 -
            (15032385536 : K[X]) * a4 ^ 2 * a5 * H ^ 32 +
            (5637144576 : K[X]) * a0 * a7 ^ 3 * H ^ 28 +
            (16911433728 : K[X]) * a1 * a6 * a7 ^ 2 * H ^ 28 +
            (16911433728 : K[X]) * a2 * a5 * a7 ^ 2 * H ^ 28 +
            (16911433728 : K[X]) * a2 * a6 ^ 2 * a7 * H ^ 28 +
            (16911433728 : K[X]) * a3 * a4 * a7 ^ 2 * H ^ 28 +
            (33822867456 : K[X]) * a3 * a5 * a6 * a7 * H ^ 28 +
            (5637144576 : K[X]) * a3 * a6 ^ 3 * H ^ 28 +
            (16911433728 : K[X]) * a4 ^ 2 * a6 * a7 * H ^ 28 +
            (16911433728 : K[X]) * a4 * a5 ^ 2 * a7 * H ^ 28 +
            (16911433728 : K[X]) * a4 * a5 * a6 ^ 2 * H ^ 28 +
            (5637144576 : K[X]) * a5 ^ 3 * a6 * H ^ 28 -
            (2994733056 : K[X]) * a1 * a7 ^ 4 * H ^ 24 -
            (11978932224 : K[X]) * a2 * a6 * a7 ^ 3 * H ^ 24 -
            (11978932224 : K[X]) * a3 * a5 * a7 ^ 3 * H ^ 24 -
            (17968398336 : K[X]) * a3 * a6 ^ 2 * a7 ^ 2 * H ^ 24 -
            (5989466112 : K[X]) * a4 ^ 2 * a7 ^ 3 * H ^ 24 -
            (35936796672 : K[X]) * a4 * a5 * a6 * a7 ^ 2 * H ^ 24 -
            (11978932224 : K[X]) * a4 * a6 ^ 3 * a7 * H ^ 24 -
            (5989466112 : K[X]) * a5 ^ 3 * a7 ^ 2 * H ^ 24 -
            (17968398336 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 * H ^ 24 -
            (2994733056 : K[X]) * a5 * a6 ^ 4 * H ^ 24 +
            (1871708160 : K[X]) * a2 * a7 ^ 5 * H ^ 20 +
            (9358540800 : K[X]) * a3 * a6 * a7 ^ 4 * H ^ 20 +
            (9358540800 : K[X]) * a4 * a5 * a7 ^ 4 * H ^ 20 +
            (18717081600 : K[X]) * a4 * a6 ^ 2 * a7 ^ 3 * H ^ 20 +
            (18717081600 : K[X]) * a5 ^ 2 * a6 * a7 ^ 3 * H ^ 20 +
            (18717081600 : K[X]) * a5 * a6 ^ 3 * a7 ^ 2 * H ^ 20 +
            (1871708160 : K[X]) * a6 ^ 5 * a7 * H ^ 20 -
            (1286799360 : K[X]) * a3 * a7 ^ 6 * H ^ 16 -
            (7720796160 : K[X]) * a4 * a6 * a7 ^ 5 * H ^ 16 -
            (3860398080 : K[X]) * a5 ^ 2 * a7 ^ 5 * H ^ 16 -
            (19301990400 : K[X]) * a5 * a6 ^ 2 * a7 ^ 4 * H ^ 16 -
            (6433996800 : K[X]) * a6 ^ 4 * a7 ^ 3 * H ^ 16 +
            (942120960 : K[X]) * a4 * a7 ^ 7 * H ^ 12 +
            (6594846720 : K[X]) * a5 * a6 * a7 ^ 6 * H ^ 12 +
            (6594846720 : K[X]) * a6 ^ 3 * a7 ^ 5 * H ^ 12 -
            (721311360 : K[X]) * a5 * a7 ^ 8 * H ^ 8 -
            (2885245440 : K[X]) * a6 ^ 2 * a7 ^ 7 * H ^ 8 +
            (571038160 : K[X]) * a6 * a7 ^ 9 * H ^ 4 -
            (42178955 : K[X]) * a7 ^ 11) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((25769803776 : K[X]) * a0 * a6 * H ^ 32 +
            (25769803776 : K[X]) * a1 * a5 * H ^ 32 +
            (25769803776 : K[X]) * a2 * a4 * H ^ 32 +
            (12884901888 : K[X]) * a3 ^ 2 * H ^ 32 -
            (3221225472 : K[X]) * a0 * a7 ^ 2 * H ^ 28 -
            (6442450944 : K[X]) * a1 * a6 * a7 * H ^ 28 -
            (6442450944 : K[X]) * a2 * a5 * a7 * H ^ 28 -
            (3221225472 : K[X]) * a2 * a6 ^ 2 * H ^ 28 -
            (6442450944 : K[X]) * a3 * a4 * a7 * H ^ 28 -
            (6442450944 : K[X]) * a3 * a5 * a6 * H ^ 28 -
            (3221225472 : K[X]) * a4 ^ 2 * a6 * H ^ 28 -
            (3221225472 : K[X]) * a4 * a5 ^ 2 * H ^ 28 +
            (1342177280 : K[X]) * a1 * a7 ^ 3 * H ^ 24 +
            (4026531840 : K[X]) * a2 * a6 * a7 ^ 2 * H ^ 24 +
            (4026531840 : K[X]) * a3 * a5 * a7 ^ 2 * H ^ 24 +
            (4026531840 : K[X]) * a3 * a6 ^ 2 * a7 * H ^ 24 +
            (2013265920 : K[X]) * a4 ^ 2 * a7 ^ 2 * H ^ 24 +
            (8053063680 : K[X]) * a4 * a5 * a6 * a7 * H ^ 24 +
            (1342177280 : K[X]) * a4 * a6 ^ 3 * H ^ 24 +
            (1342177280 : K[X]) * a5 ^ 3 * a7 * H ^ 24 +
            (2013265920 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 24 -
            (754974720 : K[X]) * a2 * a7 ^ 4 * H ^ 20 -
            (3019898880 : K[X]) * a3 * a6 * a7 ^ 3 * H ^ 20 -
            (3019898880 : K[X]) * a4 * a5 * a7 ^ 3 * H ^ 20 -
            (4529848320 : K[X]) * a4 * a6 ^ 2 * a7 ^ 2 * H ^ 20 -
            (4529848320 : K[X]) * a5 ^ 2 * a6 * a7 ^ 2 * H ^ 20 -
            (3019898880 : K[X]) * a5 * a6 ^ 3 * a7 * H ^ 20 -
            (150994944 : K[X]) * a6 ^ 5 * H ^ 20 +
            (490733568 : K[X]) * a3 * a7 ^ 5 * H ^ 16 +
            (2453667840 : K[X]) * a4 * a6 * a7 ^ 4 * H ^ 16 +
            (1226833920 : K[X]) * a5 ^ 2 * a7 ^ 4 * H ^ 16 +
            (4907335680 : K[X]) * a5 * a6 ^ 2 * a7 ^ 3 * H ^ 16 +
            (1226833920 : K[X]) * a6 ^ 4 * a7 ^ 2 * H ^ 16 -
            (347602944 : K[X]) * a4 * a7 ^ 6 * H ^ 12 -
            (2085617664 : K[X]) * a5 * a6 * a7 ^ 5 * H ^ 12 -
            (1738014720 : K[X]) * a6 ^ 3 * a7 ^ 4 * H ^ 12 +
            (260702208 : K[X]) * a5 * a7 ^ 7 * H ^ 8 +
            (912457728 : K[X]) * a6 ^ 2 * a7 ^ 6 * H ^ 8 -
            (203673600 : K[X]) * a6 * a7 ^ 8 * H ^ 4 +
            (16407040 : K[X]) * a7 ^ 10) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((1342177280 : K[X]) * a0 * a7 * H ^ 28 +
            (1342177280 : K[X]) * a1 * a6 * H ^ 28 +
            (1342177280 : K[X]) * a2 * a5 * H ^ 28 +
            (1342177280 : K[X]) * a3 * a4 * H ^ 28 -
            (251658240 : K[X]) * a1 * a7 ^ 2 * H ^ 24 -
            (503316480 : K[X]) * a2 * a6 * a7 * H ^ 24 -
            (503316480 : K[X]) * a3 * a5 * a7 * H ^ 24 -
            (251658240 : K[X]) * a3 * a6 ^ 2 * H ^ 24 -
            (251658240 : K[X]) * a4 ^ 2 * a7 * H ^ 24 -
            (503316480 : K[X]) * a4 * a5 * a6 * H ^ 24 -
            (83886080 : K[X]) * a5 ^ 3 * H ^ 24 +
            (115343360 : K[X]) * a2 * a7 ^ 3 * H ^ 20 +
            (346030080 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 20 +
            (346030080 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 20 +
            (346030080 : K[X]) * a4 * a6 ^ 2 * a7 * H ^ 20 +
            (346030080 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 20 +
            (115343360 : K[X]) * a5 * a6 ^ 3 * H ^ 20 -
            (68485120 : K[X]) * a3 * a7 ^ 4 * H ^ 16 -
            (273940480 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 16 -
            (136970240 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 16 -
            (410910720 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 16 -
            (68485120 : K[X]) * a6 ^ 4 * a7 * H ^ 16 +
            (46227456 : K[X]) * a4 * a7 ^ 5 * H ^ 12 +
            (231137280 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 12 +
            (154091520 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 12 -
            (33707520 : K[X]) * a5 * a7 ^ 6 * H ^ 8 -
            (101122560 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 8 +
            (25882560 : K[X]) * a6 * a7 ^ 7 * H ^ 4 -
            (2291685 : K[X]) * a7 ^ 9) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((1073741824 : K[X]) * a0 * H ^ 28 +
            (536870912 : K[X]) * a1 * a7 * H ^ 24 +
            (536870912 : K[X]) * a2 * a6 * H ^ 24 +
            (536870912 : K[X]) * a3 * a5 * H ^ 24 +
            (268435456 : K[X]) * a4 ^ 2 * H ^ 24 -
            (134217728 : K[X]) * a2 * a7 ^ 2 * H ^ 20 -
            (268435456 : K[X]) * a3 * a6 * a7 * H ^ 20 -
            (268435456 : K[X]) * a4 * a5 * a7 * H ^ 20 -
            (134217728 : K[X]) * a4 * a6 ^ 2 * H ^ 20 -
            (134217728 : K[X]) * a5 ^ 2 * a6 * H ^ 20 +
            (67108864 : K[X]) * a3 * a7 ^ 3 * H ^ 16 +
            (201326592 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 16 +
            (100663296 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 16 +
            (201326592 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 16 +
            (16777216 : K[X]) * a6 ^ 4 * H ^ 16 -
            (41943040 : K[X]) * a4 * a7 ^ 4 * H ^ 12 -
            (167772160 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 12 -
            (83886080 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 12 +
            (29360128 : K[X]) * a5 * a7 ^ 5 * H ^ 8 +
            (73400320 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 8 -
            (22020096 : K[X]) * a6 * a7 ^ 6 * H ^ 4 +
            (2162688 : K[X]) * a7 ^ 8) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((8388608 : K[X]) * a1 * H ^ 24 +
            (3145728 : K[X]) * a2 * a7 * H ^ 20 +
            (3145728 : K[X]) * a3 * a6 * H ^ 20 +
            (3145728 : K[X]) * a4 * a5 * H ^ 20 -
            (983040 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
            (1966080 : K[X]) * a4 * a6 * a7 * H ^ 16 -
            (983040 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
            (983040 : K[X]) * a5 * a6 ^ 2 * H ^ 16 +
            (532480 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
            (1597440 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
            (532480 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
            (349440 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
            (698880 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
            (253344 : K[X]) * a6 * a7 ^ 5 * H ^ 4 -
            (27898 : K[X]) * a7 ^ 7) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        ((2097152 : K[X]) * a2 * H ^ 20 +
            (524288 : K[X]) * a3 * a7 * H ^ 16 +
            (524288 : K[X]) * a4 * a6 * H ^ 16 +
            (262144 : K[X]) * a5 ^ 2 * H ^ 16 -
            (196608 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (393216 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (65536 : K[X]) * a6 ^ 3 * H ^ 12 +
            (114688 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (172032 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (78848 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (9856 : K[X]) * a7 ^ 6) *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        ((65536 : K[X]) * a3 * H ^ 16 +
            (8192 : K[X]) * a4 * a7 * H ^ 12 +
            (8192 : K[X]) * a5 * a6 * H ^ 12 -
            (3584 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (3584 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (2240 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (322 : K[X]) * a7 ^ 5) *
          ((2 : K[X]) * H *
              (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ).derivative -
            (63 : K[X]) *
              alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        (65536 : K[X]) * a4 * H ^ 12 *
          (H * (alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (35 : K[X]) *
              alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        ((128 : K[X]) * a5 * H ^ 8 - (16 : K[X]) * a6 * a7 * H ^ 4 +
            (3 : K[X]) * a7 ^ 3) *
          ((2 : K[X]) * H *
              (alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (77 : K[X]) *
              alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        ((32 : K[X]) * a6 * H ^ 4 - (4 : K[X]) * a7 ^ 2) *
          (H * (alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (42 : K[X]) *
              alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        a7 *
          ((2 : K[X]) * H *
              (alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (91 : K[X]) *
              alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedFourteenthDefect810, alignedThirteenthDefect810,
    alignedTwelfthDefect810, alignedEleventhDefect810,
    alignedTenthDefect810, alignedNinthDefect810,
    alignedEighthDefect810, alignedSeventhDefect810, alignedSixthDefect810,
    alignedFifthDefect810, alignedFourthDefect810, alignedThirdDefect810,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_neg, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_zero, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

set_option maxHeartbeats 1600000000 in
/-- On the aligned face, with the consumed degree-`15` through
degree-`4` rows, the degree-`3` row is the weighted derivative
`H N₁₄' - 49 N₁₄ H' = 0`. -/
theorem alignedFourteenthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H *
        (alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (49 : K[X]) *
        alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedFourteenthCoefficientJacobianRow_810 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4] at hrow
  have hrowD :
      (2 : K[X]) * H *
          (alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ).derivative -
        (21 : K[X]) *
          alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedThirdDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowE :
      H * (alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ).derivative -
        (14 : K[X]) *
          alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedFourthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowF :
      (2 : K[X]) * H *
          (alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (35 : K[X]) *
          alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedFifthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowG :
      H * (alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (21 : K[X]) *
          alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedSixthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowI :
      (2 : K[X]) * H *
          (alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (49 : K[X]) *
          alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
          H.derivative = 0 :=
    alignedSeventhDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowJ :
      H * (alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (28 : K[X]) *
          alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedEighthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowL :
      (2 : K[X]) * H *
          (alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (63 : K[X]) *
          alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedNinthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowN :
      H * (alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
        (35 : K[X]) *
          alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedTenthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowN11 :
      (2 : K[X]) * H *
          (alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (77 : K[X]) *
          alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedEleventhDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowN12 :
      H * (alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (42 : K[X]) *
          alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedTwelfthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowN13 :
      (2 : K[X]) * H *
          (alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (91 : K[X]) *
          alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedThirteenthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hid := alignedFourteenthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 0) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) κ
  rw [hrow, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ, hrowL, hrowN,
    hrowN11, hrowN12, hrowN13] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-ninety-eight polynomial first integral of the aligned
`(8,10)` fourteenth defect: `N₁₄ = κ₁₃ H⁴⁹`.  The weight is even, so
the integral is chamber-free and `κ₁₃` is preserved in both
chambers. -/
theorem alignedFourteenthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₁₃ : K,
      alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₁₃ * H ^ 49 := by
  let N : K[X] :=
    alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow :
      H * N.derivative - (49 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      alignedFourteenthDefectRow_eq_zero_810 hp hq hjac hp8 hq10
        haligned hM
  have hC49 : Polynomial.C (49 : K) = (49 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian N (H ^ 49) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      N * (Polynomial.C (49 : K) * H ^ (49 - 1) * H.derivative) -
          N.derivative * H ^ 49 =
          H ^ 48 *
            (Polynomial.C (49 : K) * N * H.derivative -
              H * N.derivative) := by
        ring
      _ = 0 := by
        rw [hC49]
        have hfac :
            (49 : K[X]) * N * H.derivative - H * N.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 49 hH) hW

/-! ## Split root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport fourteenth row at a root of its
co-factor: for the first time on an unsquared row the block splits
multiplicatively — either `g² = 4 p₆` holds at the root, or the even
dodecic core `46189 g¹² - 583440 p₆ g¹⁰ + 2759328 p₆² g⁸
- 6040320 p₆³ g⁶ + 6057216 p₆⁴ g⁴ - 2285568 p₆⁵ g² + 147456 p₆⁶`
vanishes there.  Neither branch is excluded. -/
theorem alignedFourteenth_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (2621440 : K[X]) * (g ^ 2 - (4 : K[X]) * a6) *
        ((46189 : K[X]) * g ^ 12 - (583440 : K[X]) * a6 * g ^ 10 +
          (2759328 : K[X]) * a6 ^ 2 * g ^ 8 -
          (6040320 : K[X]) * a6 ^ 3 * g ^ 6 +
          (6057216 : K[X]) * a6 ^ 4 * g ^ 4 -
          (2285568 : K[X]) * a6 ^ 5 * g ^ 2 +
          (147456 : K[X]) * a6 ^ 6) = W)
    {a : K} (hW : W.eval a = 0) :
    (g.eval a) ^ 2 = 4 * a6.eval a ∨
      46189 * (g.eval a) ^ 12 - 583440 * a6.eval a * (g.eval a) ^ 10 +
        2759328 * (a6.eval a) ^ 2 * (g.eval a) ^ 8 -
        6040320 * (a6.eval a) ^ 3 * (g.eval a) ^ 6 +
        6057216 * (a6.eval a) ^ 4 * (g.eval a) ^ 4 -
        2285568 * (a6.eval a) ^ 5 * (g.eval a) ^ 2 +
        147456 * (a6.eval a) ^ 6 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with hquad | hdodecic
  · have hq2 := (mul_eq_zero.mp hquad).resolve_left
      (by norm_num : (2621440 : K) ≠ 0)
    exact Or.inl (by linear_combination hq2)
  · exact Or.inr (by linear_combination hdodecic)

/-- The split root branch of the consumed degree-`3` row is absorbed by
the collapse of the degree-`13` face: at a root where `g` and `p₆`
already vanish the whole factored block vanishes identically, so the
fourteenth row adds no new root constraint. -/
theorem alignedFourteenth_rootQuattuordecic_absorbed_810 {K : Type*}
    [Field K] {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    2621440 * (G ^ 2 - 4 * P6) *
      (46189 * G ^ 12 - 583440 * P6 * G ^ 10 + 2759328 * P6 ^ 2 * G ^ 8 -
        6040320 * P6 ^ 3 * G ^ 6 + 6057216 * P6 ^ 4 * G ^ 4 -
        2285568 * P6 ^ 5 * G ^ 2 + 147456 * P6 ^ 6) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared fourteenth rows and transport co-factors -/

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the square-chamber fourteenth row
(`H = h₀²`, `p₇ = h₀⁴ g₁`, `h₀⁵⁶` peeled, `128 q₇ h₀²` consumed): the
`q₁` head is `17592186044416 p₃ q₁ h₀³⁴`, i.e. `q₁, …, q₆` are re-tied
at `h₀³⁴` here and at `h₀³⁸` in the cleared row. -/
def alignedFourteenthSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
    -(87960930222080 : K[X]) * a0 * a2 * h0 ^ 36 -
    (43980465111040 : K[X]) * a1 ^ 2 * h0 ^ 36 +
    (70368744177664 : K[X]) * a0 * b4 * h0 ^ 34 +
    (52776558133248 : K[X]) * a1 * b3 * h0 ^ 34 +
    (35184372088832 : K[X]) * a2 * b2 * h0 ^ 34 +
    (17592186044416 : K[X]) * a3 * b1 * h0 ^ 34 +
    (32985348833280 : K[X]) * a0 * a3 * g1 * h0 ^ 32 +
    (32985348833280 : K[X]) * a1 * a2 * g1 * h0 ^ 32 -
    (43980465111040 : K[X]) * a0 * b5 * g1 * h0 ^ 30 -
    (35184372088832 : K[X]) * a1 * b4 * g1 * h0 ^ 30 -
    (26388279066624 : K[X]) * a2 * b3 * g1 * h0 ^ 30 -
    (17592186044416 : K[X]) * a3 * b2 * g1 * h0 ^ 30 -
    (8796093022208 : K[X]) * a4 * b1 * g1 * h0 ^ 30 +
    (43980465111040 : K[X]) * a0 * a4 * a6 * h0 ^ 28 -
    (27487790694400 : K[X]) * a0 * a4 * g1 ^ 2 * h0 ^ 28 -
    (10995116277760 : K[X]) * a0 * a5 ^ 2 * h0 ^ 28 +
    (43980465111040 : K[X]) * a1 * a3 * a6 * h0 ^ 28 -
    (27487790694400 : K[X]) * a1 * a3 * g1 ^ 2 * h0 ^ 28 +
    (54975581388800 : K[X]) * a1 * a4 * a5 * h0 ^ 28 +
    (21990232555520 : K[X]) * a2 ^ 2 * a6 * h0 ^ 28 -
    (13743895347200 : K[X]) * a2 ^ 2 * g1 ^ 2 * h0 ^ 28 +
    (54975581388800 : K[X]) * a2 * a3 * a5 * h0 ^ 28 +
    (65970697666560 : K[X]) * a2 * a4 ^ 2 * h0 ^ 28 +
    (65970697666560 : K[X]) * a3 ^ 2 * a4 * h0 ^ 28 -
    (52776558133248 : K[X]) * a0 * b6 * a6 * h0 ^ 26 +
    (39582418599936 : K[X]) * a0 * b6 * g1 ^ 2 * h0 ^ 26 -
    (52776558133248 : K[X]) * a1 * a5 * b6 * h0 ^ 26 -
    (43980465111040 : K[X]) * a1 * b5 * a6 * h0 ^ 26 +
    (32985348833280 : K[X]) * a1 * b5 * g1 ^ 2 * h0 ^ 26 -
    (52776558133248 : K[X]) * a2 * a4 * b6 * h0 ^ 26 -
    (43980465111040 : K[X]) * a2 * a5 * b5 * h0 ^ 26 -
    (35184372088832 : K[X]) * a2 * b4 * a6 * h0 ^ 26 +
    (26388279066624 : K[X]) * a2 * b4 * g1 ^ 2 * h0 ^ 26 -
    (26388279066624 : K[X]) * a3 ^ 2 * b6 * h0 ^ 26 -
    (43980465111040 : K[X]) * a3 * a4 * b5 * h0 ^ 26 -
    (35184372088832 : K[X]) * a3 * a5 * b4 * h0 ^ 26 -
    (26388279066624 : K[X]) * a3 * b3 * a6 * h0 ^ 26 +
    (19791209299968 : K[X]) * a3 * b3 * g1 ^ 2 * h0 ^ 26 -
    (17592186044416 : K[X]) * a4 ^ 2 * b4 * h0 ^ 26 -
    (26388279066624 : K[X]) * a4 * a5 * b3 * h0 ^ 26 -
    (17592186044416 : K[X]) * a4 * b2 * a6 * h0 ^ 26 +
    (13194139533312 : K[X]) * a4 * b2 * g1 ^ 2 * h0 ^ 26 -
    (8796093022208 : K[X]) * a5 ^ 2 * b2 * h0 ^ 26 -
    (8796093022208 : K[X]) * a5 * b1 * a6 * h0 ^ 26 +
    (6597069766656 : K[X]) * a5 * b1 * g1 ^ 2 * h0 ^ 26 +
    (46729244180480 : K[X]) * a0 * a5 * a6 * g1 * h0 ^ 24 -
    (22333829939200 : K[X]) * a0 * a5 * g1 ^ 3 * h0 ^ 24 -
    (68719476736000 : K[X]) * a1 * a4 * a6 * g1 * h0 ^ 24 +
    (25769803776000 : K[X]) * a1 * a4 * g1 ^ 3 * h0 ^ 24 +
    (24739011624960 : K[X]) * a1 * a5 ^ 2 * g1 * h0 ^ 24 -
    (68719476736000 : K[X]) * a2 * a3 * a6 * g1 * h0 ^ 24 +
    (25769803776000 : K[X]) * a2 * a3 * g1 ^ 3 * h0 ^ 24 -
    (65970697666560 : K[X]) * a2 * a4 * a5 * g1 * h0 ^ 24 -
    (32985348833280 : K[X]) * a3 ^ 2 * a5 * g1 * h0 ^ 24 -
    (90709709291520 : K[X]) * a3 * a4 ^ 2 * g1 * h0 ^ 24 +
    (79164837199872 : K[X]) * a1 * b6 * a6 * g1 * h0 ^ 22 -
    (32985348833280 : K[X]) * a1 * b6 * g1 ^ 3 * h0 ^ 22 +
    (79164837199872 : K[X]) * a2 * a5 * b6 * g1 * h0 ^ 22 +
    (65970697666560 : K[X]) * a2 * b5 * a6 * g1 * h0 ^ 22 -
    (27487790694400 : K[X]) * a2 * b5 * g1 ^ 3 * h0 ^ 22 +
    (79164837199872 : K[X]) * a3 * a4 * b6 * g1 * h0 ^ 22 +
    (65970697666560 : K[X]) * a3 * a5 * b5 * g1 * h0 ^ 22 +
    (52776558133248 : K[X]) * a3 * b4 * a6 * g1 * h0 ^ 22 -
    (21990232555520 : K[X]) * a3 * b4 * g1 ^ 3 * h0 ^ 22 +
    (32985348833280 : K[X]) * a4 ^ 2 * b5 * g1 * h0 ^ 22 +
    (52776558133248 : K[X]) * a4 * a5 * b4 * g1 * h0 ^ 22 +
    (39582418599936 : K[X]) * a4 * b3 * a6 * g1 * h0 ^ 22 -
    (16492674416640 : K[X]) * a4 * b3 * g1 ^ 3 * h0 ^ 22 +
    (19791209299968 : K[X]) * a5 ^ 2 * b3 * g1 * h0 ^ 22 +
    (26388279066624 : K[X]) * a5 * b2 * a6 * g1 * h0 ^ 22 -
    (10995116277760 : K[X]) * a5 * b2 * g1 ^ 3 * h0 ^ 22 +
    (6597069766656 : K[X]) * b1 * a6 ^ 2 * g1 * h0 ^ 22 -
    (5497558138880 : K[X]) * b1 * a6 * g1 ^ 3 * h0 ^ 22 +
    (962072674304 : K[X]) * b1 * g1 ^ 5 * h0 ^ 22 +
    (10995116277760 : K[X]) * a0 * a6 ^ 3 * h0 ^ 20 -
    (24739011624960 : K[X]) * a0 * a6 ^ 2 * g1 ^ 2 * h0 ^ 20 +
    (11854109736960 : K[X]) * a0 * a6 * g1 ^ 4 * h0 ^ 20 -
    (1503238553600 : K[X]) * a0 * g1 ^ 6 * h0 ^ 20 +
    (24739011624960 : K[X]) * a1 * a5 * a6 ^ 2 * h0 ^ 20 -
    (57724360458240 : K[X]) * a1 * a5 * a6 * g1 ^ 2 * h0 ^ 20 +
    (17867063951360 : K[X]) * a1 * a5 * g1 ^ 4 * h0 ^ 20 -
    (32985348833280 : K[X]) * a2 * a4 * a6 ^ 2 * h0 ^ 20 +
    (86586540687360 : K[X]) * a2 * a4 * a6 * g1 ^ 2 * h0 ^ 20 -
    (24223615549440 : K[X]) * a2 * a4 * g1 ^ 4 * h0 ^ 20 +
    (16492674416640 : K[X]) * a2 * a5 ^ 2 * a6 * h0 ^ 20 -
    (32985348833280 : K[X]) * a2 * a5 ^ 2 * g1 ^ 2 * h0 ^ 20 -
    (16492674416640 : K[X]) * a3 ^ 2 * a6 ^ 2 * h0 ^ 20 +
    (43293270343680 : K[X]) * a3 ^ 2 * a6 * g1 ^ 2 * h0 ^ 20 -
    (12111807774720 : K[X]) * a3 ^ 2 * g1 ^ 4 * h0 ^ 20 -
    (82463372083200 : K[X]) * a3 * a4 * a5 * a6 * h0 ^ 20 +
    (78340203479040 : K[X]) * a3 * a4 * a5 * g1 ^ 2 * h0 ^ 20 +
    (2748779069440 : K[X]) * a3 * a5 ^ 3 * h0 ^ 20 -
    (32985348833280 : K[X]) * a4 ^ 3 * a6 * h0 ^ 20 +
    (37108517437440 : K[X]) * a4 ^ 3 * g1 ^ 2 * h0 ^ 20 -
    (24739011624960 : K[X]) * a4 ^ 2 * a5 ^ 2 * h0 ^ 20 +
    (39582418599936 : K[X]) * a2 * b6 * a6 ^ 2 * h0 ^ 18 -
    (98956046499840 : K[X]) * a2 * b6 * a6 * g1 ^ 2 * h0 ^ 18 +
    (28862180229120 : K[X]) * a2 * b6 * g1 ^ 4 * h0 ^ 18 +
    (79164837199872 : K[X]) * a3 * a5 * b6 * a6 * h0 ^ 18 -
    (98956046499840 : K[X]) * a3 * a5 * b6 * g1 ^ 2 * h0 ^ 18 +
    (32985348833280 : K[X]) * a3 * b5 * a6 ^ 2 * h0 ^ 18 -
    (82463372083200 : K[X]) * a3 * b5 * a6 * g1 ^ 2 * h0 ^ 18 +
    (24051816857600 : K[X]) * a3 * b5 * g1 ^ 4 * h0 ^ 18 +
    (39582418599936 : K[X]) * a4 ^ 2 * b6 * a6 * h0 ^ 18 -
    (49478023249920 : K[X]) * a4 ^ 2 * b6 * g1 ^ 2 * h0 ^ 18 +
    (39582418599936 : K[X]) * a4 * a5 ^ 2 * b6 * h0 ^ 18 +
    (65970697666560 : K[X]) * a4 * a5 * b5 * a6 * h0 ^ 18 -
    (82463372083200 : K[X]) * a4 * a5 * b5 * g1 ^ 2 * h0 ^ 18 +
    (26388279066624 : K[X]) * a4 * b4 * a6 ^ 2 * h0 ^ 18 -
    (65970697666560 : K[X]) * a4 * b4 * a6 * g1 ^ 2 * h0 ^ 18 +
    (19241453486080 : K[X]) * a4 * b4 * g1 ^ 4 * h0 ^ 18 +
    (10995116277760 : K[X]) * a5 ^ 3 * b5 * h0 ^ 18 +
    (26388279066624 : K[X]) * a5 ^ 2 * b4 * a6 * h0 ^ 18 -
    (32985348833280 : K[X]) * a5 ^ 2 * b4 * g1 ^ 2 * h0 ^ 18 +
    (19791209299968 : K[X]) * a5 * b3 * a6 ^ 2 * h0 ^ 18 -
    (49478023249920 : K[X]) * a5 * b3 * a6 * g1 ^ 2 * h0 ^ 18 +
    (14431090114560 : K[X]) * a5 * b3 * g1 ^ 4 * h0 ^ 18 +
    (4398046511104 : K[X]) * b2 * a6 ^ 3 * h0 ^ 18 -
    (16492674416640 : K[X]) * b2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 18 +
    (9620726743040 : K[X]) * b2 * a6 * g1 ^ 4 * h0 ^ 18 -
    (1443109011456 : K[X]) * b2 * g1 ^ 6 * h0 ^ 18 -
    (19928648253440 : K[X]) * a1 * a6 ^ 3 * g1 * h0 ^ 16 +
    (25683904430080 : K[X]) * a1 * a6 ^ 2 * g1 ^ 3 * h0 ^ 16 -
    (9620726743040 : K[X]) * a1 * a6 * g1 ^ 5 * h0 ^ 16 +
    (1068373114880 : K[X]) * a1 * g1 ^ 7 * h0 ^ 16 -
    (53601191854080 : K[X]) * a2 * a5 * a6 ^ 2 * g1 * h0 ^ 16 +
    (63393717288960 : K[X]) * a2 * a5 * a6 * g1 ^ 3 * h0 ^ 16 -
    (14731737825280 : K[X]) * a2 * a5 * g1 ^ 5 * h0 ^ 16 +
    (90709709291520 : K[X]) * a3 * a4 * a6 ^ 2 * g1 * h0 ^ 16 -
    (104969000714240 : K[X]) * a3 * a4 * a6 * g1 ^ 3 * h0 ^ 16 +
    (23149873725440 : K[X]) * a3 * a4 * g1 ^ 5 * h0 ^ 16 -
    (47416438947840 : K[X]) * a3 * a5 ^ 2 * a6 * g1 * h0 ^ 16 +
    (37709812858880 : K[X]) * a3 * a5 ^ 2 * g1 ^ 3 * h0 ^ 16 +
    (96894462197760 : K[X]) * a4 ^ 2 * a5 * a6 * g1 * h0 ^ 16 -
    (46471546142720 : K[X]) * a4 ^ 2 * a5 * g1 ^ 3 * h0 ^ 16 -
    (13743895347200 : K[X]) * a4 * a5 ^ 3 * g1 * h0 ^ 16 -
    (98956046499840 : K[X]) * a3 * b6 * a6 ^ 2 * g1 * h0 ^ 14 +
    (115448720916480 : K[X]) * a3 * b6 * a6 * g1 ^ 3 * h0 ^ 14 -
    (25975962206208 : K[X]) * a3 * b6 * g1 ^ 5 * h0 ^ 14 -
    (197912092999680 : K[X]) * a4 * a5 * b6 * a6 * g1 * h0 ^ 14 +
    (115448720916480 : K[X]) * a4 * a5 * b6 * g1 ^ 3 * h0 ^ 14 -
    (82463372083200 : K[X]) * a4 * b5 * a6 ^ 2 * g1 * h0 ^ 14 +
    (96207267430400 : K[X]) * a4 * b5 * a6 * g1 ^ 3 * h0 ^ 14 -
    (21646635171840 : K[X]) * a4 * b5 * g1 ^ 5 * h0 ^ 14 -
    (32985348833280 : K[X]) * a5 ^ 3 * b6 * g1 * h0 ^ 14 -
    (82463372083200 : K[X]) * a5 ^ 2 * b5 * a6 * g1 * h0 ^ 14 +
    (48103633715200 : K[X]) * a5 ^ 2 * b5 * g1 ^ 3 * h0 ^ 14 -
    (65970697666560 : K[X]) * a5 * b4 * a6 ^ 2 * g1 * h0 ^ 14 +
    (76965813944320 : K[X]) * a5 * b4 * a6 * g1 ^ 3 * h0 ^ 14 -
    (17317308137472 : K[X]) * a5 * b4 * g1 ^ 5 * h0 ^ 14 -
    (16492674416640 : K[X]) * b3 * a6 ^ 3 * g1 * h0 ^ 14 +
    (28862180229120 : K[X]) * b3 * a6 ^ 2 * g1 ^ 3 * h0 ^ 14 -
    (12987981103104 : K[X]) * b3 * a6 * g1 ^ 5 * h0 ^ 14 +
    (1700807049216 : K[X]) * b3 * g1 ^ 7 * h0 ^ 14 -
    (6871947673600 : K[X]) * a2 * a6 ^ 4 * h0 ^ 12 +
    (29205777612800 : K[X]) * a2 * a6 ^ 3 * g1 ^ 2 * h0 ^ 12 -
    (25555055411200 : K[X]) * a2 * a6 ^ 2 * g1 ^ 4 * h0 ^ 12 +
    (7816840478720 : K[X]) * a2 * a6 * g1 ^ 6 * h0 ^ 12 -
    (765041049600 : K[X]) * a2 * g1 ^ 8 * h0 ^ 12 -
    (20615843020800 : K[X]) * a3 * a5 * a6 ^ 3 * h0 ^ 12 +
    (87617332838400 : K[X]) * a3 * a5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 12 -
    (66142496358400 : K[X]) * a3 * a5 * a6 * g1 ^ 4 * h0 ^ 12 +
    (12326556139520 : K[X]) * a3 * a5 * g1 ^ 6 * h0 ^ 12 +
    (13743895347200 : K[X]) * a4 ^ 2 * a6 ^ 3 * h0 ^ 12 -
    (82463372083200 : K[X]) * a4 ^ 2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 12 +
    (61632780697600 : K[X]) * a4 ^ 2 * a6 * g1 ^ 4 * h0 ^ 12 -
    (11199127224320 : K[X]) * a4 ^ 2 * g1 ^ 6 * h0 ^ 12 -
    (20615843020800 : K[X]) * a4 * a5 ^ 2 * a6 ^ 2 * h0 ^ 12 +
    (87617332838400 : K[X]) * a4 * a5 ^ 2 * a6 * g1 ^ 2 * h0 ^ 12 -
    (40587440947200 : K[X]) * a4 * a5 ^ 2 * g1 ^ 4 * h0 ^ 12 -
    (13743895347200 : K[X]) * a5 ^ 4 * a6 * h0 ^ 12 +
    (28346784153600 : K[X]) * a5 ^ 4 * g1 ^ 2 * h0 ^ 12 -
    (32985348833280 : K[X]) * a4 * b6 * a6 ^ 3 * h0 ^ 10 +
    (173173081374720 : K[X]) * a4 * b6 * a6 ^ 2 * g1 ^ 2 * h0 ^ 10 -
    (129879811031040 : K[X]) * a4 * b6 * a6 * g1 ^ 4 * h0 ^ 10 +
    (23811298689024 : K[X]) * a4 * b6 * g1 ^ 6 * h0 ^ 10 -
    (49478023249920 : K[X]) * a5 ^ 2 * b6 * a6 ^ 2 * h0 ^ 10 +
    (173173081374720 : K[X]) * a5 ^ 2 * b6 * a6 * g1 ^ 2 * h0 ^ 10 -
    (64939905515520 : K[X]) * a5 ^ 2 * b6 * g1 ^ 4 * h0 ^ 10 -
    (27487790694400 : K[X]) * a5 * b5 * a6 ^ 3 * h0 ^ 10 +
    (144310901145600 : K[X]) * a5 * b5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 10 -
    (108233175859200 : K[X]) * a5 * b5 * a6 * g1 ^ 4 * h0 ^ 10 +
    (19842748907520 : K[X]) * a5 * b5 * g1 ^ 6 * h0 ^ 10 -
    (5497558138880 : K[X]) * b4 * a6 ^ 4 * h0 ^ 10 +
    (38482906972160 : K[X]) * b4 * a6 ^ 3 * g1 ^ 2 * h0 ^ 10 -
    (43293270343680 : K[X]) * b4 * a6 ^ 2 * g1 ^ 4 * h0 ^ 10 +
    (15874199126016 : K[X]) * b4 * a6 * g1 ^ 6 * h0 ^ 10 -
    (1842540969984 : K[X]) * b4 * g1 ^ 8 * h0 ^ 10 +
    (18038862643200 : K[X]) * a3 * a6 ^ 4 * g1 * h0 ^ 8 -
    (37580963840000 : K[X]) * a3 * a6 ^ 3 * g1 ^ 3 * h0 ^ 8 +
    (24577950351360 : K[X]) * a3 * a6 ^ 2 * g1 ^ 5 * h0 ^ 8 -
    (6305548861440 : K[X]) * a3 * a6 * g1 ^ 7 * h0 ^ 8 +
    (546266152960 : K[X]) * a3 * g1 ^ 9 * h0 ^ 8 +
    (60129542144000 : K[X]) * a4 * a5 * a6 ^ 3 * g1 * h0 ^ 8 -
    (121762322841600 : K[X]) * a4 * a5 * a6 ^ 2 * g1 ^ 3 * h0 ^ 8 +
    (66743791779840 : K[X]) * a4 * a5 * a6 * g1 ^ 5 * h0 ^ 8 -
    (10380399083520 : K[X]) * a4 * a5 * g1 ^ 7 * h0 ^ 8 +
    (108233175859200 : K[X]) * a5 ^ 3 * a6 ^ 2 * g1 * h0 ^ 8 -
    (169865956556800 : K[X]) * a5 ^ 3 * a6 * g1 ^ 3 * h0 ^ 8 +
    (48780091064320 : K[X]) * a5 ^ 3 * g1 ^ 5 * h0 ^ 8 +
    (115448720916480 : K[X]) * a5 * b6 * a6 ^ 3 * g1 * h0 ^ 6 -
    (259759622062080 : K[X]) * a5 * b6 * a6 ^ 2 * g1 ^ 3 * h0 ^ 6 +
    (142867792134144 : K[X]) * a5 * b6 * a6 * g1 ^ 5 * h0 ^ 6 -
    (22110491639808 : K[X]) * a5 * b6 * g1 ^ 7 * h0 ^ 6 +
    (24051816857600 : K[X]) * b5 * a6 ^ 4 * g1 * h0 ^ 6 -
    (72155450572800 : K[X]) * b5 * a6 ^ 3 * g1 ^ 3 * h0 ^ 6 +
    (59528246722560 : K[X]) * b5 * a6 ^ 2 * g1 ^ 5 * h0 ^ 6 -
    (18425409699840 : K[X]) * b5 * a6 * g1 ^ 7 * h0 ^ 6 +
    (1919313510400 : K[X]) * b5 * g1 ^ 9 * h0 ^ 6 +
    (4810363371520 : K[X]) * a4 * a6 ^ 5 * h0 ^ 4 -
    (33071248179200 : K[X]) * a4 * a6 ^ 4 * g1 ^ 2 * h0 ^ 4 +
    (44345537331200 : K[X]) * a4 * a6 ^ 3 * g1 ^ 4 * h0 ^ 4 -
    (22886806978560 : K[X]) * a4 * a6 ^ 2 * g1 ^ 6 * h0 ^ 4 +
    (5004979077120 : K[X]) * a4 * a6 * g1 ^ 8 * h0 ^ 4 -
    (383862702080 : K[X]) * a4 * g1 ^ 10 * h0 ^ 4 +
    (30064771072000 : K[X]) * a5 ^ 2 * a6 ^ 4 * h0 ^ 4 -
    (249537599897600 : K[X]) * a5 ^ 2 * a6 ^ 3 * g1 ^ 2 * h0 ^ 4 +
    (337101245644800 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 ^ 4 * h0 ^ 4 -
    (145663815843840 : K[X]) * a5 ^ 2 * a6 * g1 ^ 6 * h0 ^ 4 +
    (19488414105600 : K[X]) * a5 ^ 2 * g1 ^ 8 * h0 ^ 4 +
    (5772436045824 : K[X]) * b6 * a6 ^ 5 * h0 ^ 2 -
    (64939905515520 : K[X]) * b6 * a6 ^ 4 * g1 ^ 2 * h0 ^ 2 +
    (119056493445120 : K[X]) * b6 * a6 ^ 3 * g1 ^ 4 * h0 ^ 2 -
    (77386720739328 : K[X]) * b6 * a6 ^ 2 * g1 ^ 6 * h0 ^ 2 +
    (20728585912320 : K[X]) * b6 * a6 * g1 ^ 8 * h0 ^ 2 -
    (1957699780608 : K[X]) * b6 * g1 ^ 10 * h0 ^ 2 -
    (54417235640320 : K[X]) * a5 * a6 ^ 5 * g1 +
    (224170449305600 : K[X]) * a5 * a6 ^ 4 * g1 ^ 3 -
    (274641683742720 : K[X]) * a5 * a6 ^ 3 * g1 ^ 5 +
    (141490315591680 : K[X]) * a5 * a6 ^ 2 * g1 ^ 7 -
    (32412406906880 : K[X]) * a5 * a6 * g1 ^ 9 +
    (2726024970240 : K[X]) * a5 * g1 ^ 11 +
    Polynomial.C κ *
      (-(2199023255552 : K[X]) * a0 * a4 * h0 ^ 34 -
        (2199023255552 : K[X]) * a1 * a3 * h0 ^ 34 -
        (1099511627776 : K[X]) * a2 ^ 2 * h0 ^ 34 +
        (1374389534720 : K[X]) * a0 * a5 * g1 * h0 ^ 30 +
        (1374389534720 : K[X]) * a1 * a4 * g1 * h0 ^ 30 +
        (1374389534720 : K[X]) * a2 * a3 * g1 * h0 ^ 30 +
        (1649267441664 : K[X]) * a0 * a6 ^ 2 * h0 ^ 26 -
        (1236950581248 : K[X]) * a0 * a6 * g1 ^ 2 * h0 ^ 26 +
        (3298534883328 : K[X]) * a1 * a5 * a6 * h0 ^ 26 -
        (1236950581248 : K[X]) * a1 * a5 * g1 ^ 2 * h0 ^ 26 +
        (3298534883328 : K[X]) * a2 * a4 * a6 * h0 ^ 26 -
        (1236950581248 : K[X]) * a2 * a4 * g1 ^ 2 * h0 ^ 26 +
        (1649267441664 : K[X]) * a2 * a5 ^ 2 * h0 ^ 26 +
        (1649267441664 : K[X]) * a3 ^ 2 * a6 * h0 ^ 26 -
        (618475290624 : K[X]) * a3 ^ 2 * g1 ^ 2 * h0 ^ 26 +
        (3298534883328 : K[X]) * a3 * a4 * a5 * h0 ^ 26 +
        (549755813888 : K[X]) * a4 ^ 3 * h0 ^ 26 -
        (2680059592704 : K[X]) * a1 * a6 ^ 2 * g1 * h0 ^ 22 +
        (1202590842880 : K[X]) * a1 * a6 * g1 ^ 3 * h0 ^ 22 -
        (30064771072 : K[X]) * a1 * g1 ^ 5 * h0 ^ 22 -
        (5360119185408 : K[X]) * a2 * a5 * a6 * g1 * h0 ^ 22 +
        (1202590842880 : K[X]) * a2 * a5 * g1 ^ 3 * h0 ^ 22 -
        (5360119185408 : K[X]) * a3 * a4 * a6 * g1 * h0 ^ 22 +
        (1202590842880 : K[X]) * a3 * a4 * g1 ^ 3 * h0 ^ 22 -
        (2680059592704 : K[X]) * a3 * a5 ^ 2 * g1 * h0 ^ 22 -
        (2680059592704 : K[X]) * a4 ^ 2 * a5 * g1 * h0 ^ 22 -
        (1374389534720 : K[X]) * a2 * a6 ^ 3 * h0 ^ 18 +
        (3607772528640 : K[X]) * a2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 18 -
        (1202590842880 : K[X]) * a2 * a6 * g1 ^ 4 * h0 ^ 18 +
        (45097156608 : K[X]) * a2 * g1 ^ 6 * h0 ^ 18 -
        (4123168604160 : K[X]) * a3 * a5 * a6 ^ 2 * h0 ^ 18 +
        (7215545057280 : K[X]) * a3 * a5 * a6 * g1 ^ 2 * h0 ^ 18 -
        (1202590842880 : K[X]) * a3 * a5 * g1 ^ 4 * h0 ^ 18 -
        (2061584302080 : K[X]) * a4 ^ 2 * a6 ^ 2 * h0 ^ 18 +
        (3607772528640 : K[X]) * a4 ^ 2 * a6 * g1 ^ 2 * h0 ^ 18 -
        (601295421440 : K[X]) * a4 ^ 2 * g1 ^ 4 * h0 ^ 18 -
        (4123168604160 : K[X]) * a4 * a5 ^ 2 * a6 * h0 ^ 18 +
        (3607772528640 : K[X]) * a4 * a5 ^ 2 * g1 ^ 2 * h0 ^ 18 -
        (343597383680 : K[X]) * a5 ^ 4 * h0 ^ 18 +
        (3607772528640 : K[X]) * a3 * a6 ^ 3 * g1 * h0 ^ 14 -
        (4509715660800 : K[X]) * a3 * a6 ^ 2 * g1 ^ 3 * h0 ^ 14 +
        (1217623228416 : K[X]) * a3 * a6 * g1 ^ 5 * h0 ^ 14 -
        (53150220288 : K[X]) * a3 * g1 ^ 7 * h0 ^ 14 +
        (10823317585920 : K[X]) * a4 * a5 * a6 ^ 2 * g1 * h0 ^ 14 -
        (9019431321600 : K[X]) * a4 * a5 * a6 * g1 ^ 3 * h0 ^ 14 +
        (1217623228416 : K[X]) * a4 * a5 * g1 ^ 5 * h0 ^ 14 +
        (3607772528640 : K[X]) * a5 ^ 3 * a6 * g1 * h0 ^ 14 -
        (1503238553600 : K[X]) * a5 ^ 3 * g1 ^ 3 * h0 ^ 14 +
        (1202590842880 : K[X]) * a4 * a6 ^ 4 * h0 ^ 10 -
        (6614249635840 : K[X]) * a4 * a6 ^ 3 * g1 ^ 2 * h0 ^ 10 +
        (5411658792960 : K[X]) * a4 * a6 ^ 2 * g1 ^ 4 * h0 ^ 10 -
        (1240171806720 : K[X]) * a4 * a6 * g1 ^ 6 * h0 ^ 10 +
        (57579405312 : K[X]) * a4 * g1 ^ 8 * h0 ^ 10 +
        (2405181685760 : K[X]) * a5 ^ 2 * a6 ^ 3 * h0 ^ 10 -
        (9921374453760 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 10 +
        (5411658792960 : K[X]) * a5 ^ 2 * a6 * g1 ^ 4 * h0 ^ 10 -
        (620085903360 : K[X]) * a5 ^ 2 * g1 ^ 6 * h0 ^ 10 -
        (4359391805440 : K[X]) * a5 * a6 ^ 4 * g1 * h0 ^ 6 +
        (10372346019840 : K[X]) * a5 * a6 ^ 3 * g1 ^ 3 * h0 ^ 6 -
        (6324876214272 : K[X]) * a5 * a6 ^ 2 * g1 ^ 5 * h0 ^ 6 +
        (1266746916864 : K[X]) * a5 * a6 * g1 ^ 7 * h0 ^ 6 -
        (59978547200 : K[X]) * a5 * g1 ^ 9 * h0 ^ 6 -
        (180388626432 : K[X]) * a6 ^ 6 * h0 ^ 2 +
        (2029372047360 : K[X]) * a6 ^ 5 * g1 ^ 2 * h0 ^ 2 -
        (3720515420160 : K[X]) * a6 ^ 4 * g1 ^ 4 * h0 ^ 2 +
        (2418335023104 : K[X]) * a6 ^ 3 * g1 ^ 6 * h0 ^ 2 -
        (647768309760 : K[X]) * a6 ^ 2 * g1 ^ 8 * h0 ^ 2 +
        (61178118144 : K[X]) * a6 * g1 ^ 10 * h0 ^ 2) -
    Polynomial.C μ *
      (-(481036337152 : K[X]) * a0 * a5 * h0 ^ 33 -
        (481036337152 : K[X]) * a1 * a4 * h0 ^ 33 -
        (481036337152 : K[X]) * a2 * a3 * h0 ^ 33 +
        (721554505728 : K[X]) * a0 * a6 * g1 * h0 ^ 29 -
        (300647710720 : K[X]) * a0 * g1 ^ 3 * h0 ^ 29 +
        (721554505728 : K[X]) * a1 * a5 * g1 * h0 ^ 29 +
        (721554505728 : K[X]) * a2 * a4 * g1 * h0 ^ 29 +
        (360777252864 : K[X]) * a3 ^ 2 * g1 * h0 ^ 29 +
        (360777252864 : K[X]) * a1 * a6 ^ 2 * h0 ^ 25 -
        (901943132160 : K[X]) * a1 * a6 * g1 ^ 2 * h0 ^ 25 +
        (263066746880 : K[X]) * a1 * g1 ^ 4 * h0 ^ 25 +
        (721554505728 : K[X]) * a2 * a5 * a6 * h0 ^ 25 -
        (901943132160 : K[X]) * a2 * a5 * g1 ^ 2 * h0 ^ 25 +
        (721554505728 : K[X]) * a3 * a4 * a6 * h0 ^ 25 -
        (901943132160 : K[X]) * a3 * a4 * g1 ^ 2 * h0 ^ 25 +
        (360777252864 : K[X]) * a3 * a5 ^ 2 * h0 ^ 25 +
        (360777252864 : K[X]) * a4 ^ 2 * a5 * h0 ^ 25 -
        (901943132160 : K[X]) * a2 * a6 ^ 2 * g1 * h0 ^ 21 +
        (1052266987520 : K[X]) * a2 * a6 * g1 ^ 3 * h0 ^ 21 -
        (236760072192 : K[X]) * a2 * g1 ^ 5 * h0 ^ 21 -
        (1803886264320 : K[X]) * a3 * a5 * a6 * g1 * h0 ^ 21 +
        (1052266987520 : K[X]) * a3 * a5 * g1 ^ 3 * h0 ^ 21 -
        (901943132160 : K[X]) * a4 ^ 2 * a6 * g1 * h0 ^ 21 +
        (526133493760 : K[X]) * a4 ^ 2 * g1 ^ 3 * h0 ^ 21 -
        (901943132160 : K[X]) * a4 * a5 ^ 2 * g1 * h0 ^ 21 -
        (300647710720 : K[X]) * a3 * a6 ^ 3 * h0 ^ 17 +
        (1578400481280 : K[X]) * a3 * a6 ^ 2 * g1 ^ 2 * h0 ^ 17 -
        (1183800360960 : K[X]) * a3 * a6 * g1 ^ 4 * h0 ^ 17 +
        (217030066176 : K[X]) * a3 * g1 ^ 6 * h0 ^ 17 -
        (901943132160 : K[X]) * a4 * a5 * a6 ^ 2 * h0 ^ 17 +
        (3156800962560 : K[X]) * a4 * a5 * a6 * g1 ^ 2 * h0 ^ 17 -
        (1183800360960 : K[X]) * a4 * a5 * g1 ^ 4 * h0 ^ 17 -
        (300647710720 : K[X]) * a5 ^ 3 * a6 * h0 ^ 17 +
        (526133493760 : K[X]) * a5 ^ 3 * g1 ^ 2 * h0 ^ 17 +
        (1052266987520 : K[X]) * a4 * a6 ^ 3 * g1 * h0 ^ 13 -
        (2367600721920 : K[X]) * a4 * a6 ^ 2 * g1 ^ 3 * h0 ^ 13 +
        (1302180397056 : K[X]) * a4 * a6 * g1 ^ 5 * h0 ^ 13 -
        (201527918592 : K[X]) * a4 * g1 ^ 7 * h0 ^ 13 +
        (1578400481280 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 * h0 ^ 13 -
        (2367600721920 : K[X]) * a5 ^ 2 * a6 * g1 ^ 3 * h0 ^ 13 +
        (651090198528 : K[X]) * a5 ^ 2 * g1 ^ 5 * h0 ^ 13 +
        (263066746880 : K[X]) * a5 * a6 ^ 4 * h0 ^ 9 -
        (2367600721920 : K[X]) * a5 * a6 ^ 3 * g1 ^ 2 * h0 ^ 9 +
        (3255450992640 : K[X]) * a5 * a6 ^ 2 * g1 ^ 4 * h0 ^ 9 -
        (1410695430144 : K[X]) * a5 * a6 * g1 ^ 6 * h0 ^ 9 +
        (188932423680 : K[X]) * a5 * g1 ^ 8 * h0 ^ 9 -
        (236760072192 : K[X]) * a6 ^ 5 * g1 * h0 ^ 5 +
        (1085150330880 : K[X]) * a6 ^ 4 * g1 ^ 3 * h0 ^ 5 -
        (1410695430144 : K[X]) * a6 ^ 3 * g1 ^ 5 * h0 ^ 5 +
        (755729694720 : K[X]) * a6 ^ 2 * g1 ^ 7 * h0 ^ 5 -
        (178436177920 : K[X]) * a6 * g1 ^ 9 * h0 ^ 5 +
        (15410397184 : K[X]) * g1 ^ 11 * h0 ^ 5)

/-- Cleared fourteenth row of the square chamber, in factored form:
`h₀⁴` times the transport co-factor plus the split `g₁, p₆` block
`2621440 (g₁² - 4 p₆)` times the even dodecic. -/
def alignedFourteenthSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedFourteenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ μ +
    (2621440 : K[X]) * (g1 ^ 2 - (4 : K[X]) * a6) *
      ((46189 : K[X]) * g1 ^ 12 - (583440 : K[X]) * a6 * g1 ^ 10 +
        (2759328 : K[X]) * a6 ^ 2 * g1 ^ 8 -
        (6040320 : K[X]) * a6 ^ 3 * g1 ^ 6 +
        (6057216 : K[X]) * a6 ^ 4 * g1 ^ 4 -
        (2285568 : K[X]) * a6 ^ 5 * g1 ^ 2 +
        (147456 : K[X]) * a6 ^ 6)

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the nonsquare-chamber fourteenth row
(`p₇ = H² g₂`, `H²⁸` peeled, `128 q₇ H` consumed): the `q₁` head is
`17592186044416 p₃ q₁ H¹⁷`, i.e. `q₁, …, q₆` sit at `H¹⁹` in the
cleared row. -/
def alignedFourteenthNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(87960930222080 : K[X]) * a0 * a2 * H ^ 18 -
    (43980465111040 : K[X]) * a1 ^ 2 * H ^ 18 +
    (70368744177664 : K[X]) * a0 * b4 * H ^ 17 +
    (52776558133248 : K[X]) * a1 * b3 * H ^ 17 +
    (35184372088832 : K[X]) * a2 * b2 * H ^ 17 +
    (17592186044416 : K[X]) * a3 * b1 * H ^ 17 +
    (32985348833280 : K[X]) * a0 * a3 * g2 * H ^ 16 +
    (32985348833280 : K[X]) * a1 * a2 * g2 * H ^ 16 -
    (43980465111040 : K[X]) * a0 * b5 * g2 * H ^ 15 -
    (35184372088832 : K[X]) * a1 * b4 * g2 * H ^ 15 -
    (26388279066624 : K[X]) * a2 * b3 * g2 * H ^ 15 -
    (17592186044416 : K[X]) * a3 * b2 * g2 * H ^ 15 -
    (8796093022208 : K[X]) * a4 * b1 * g2 * H ^ 15 +
    (43980465111040 : K[X]) * a0 * a4 * a6 * H ^ 14 -
    (27487790694400 : K[X]) * a0 * a4 * g2 ^ 2 * H ^ 14 -
    (10995116277760 : K[X]) * a0 * a5 ^ 2 * H ^ 14 +
    (43980465111040 : K[X]) * a1 * a3 * a6 * H ^ 14 -
    (27487790694400 : K[X]) * a1 * a3 * g2 ^ 2 * H ^ 14 +
    (54975581388800 : K[X]) * a1 * a4 * a5 * H ^ 14 +
    (21990232555520 : K[X]) * a2 ^ 2 * a6 * H ^ 14 -
    (13743895347200 : K[X]) * a2 ^ 2 * g2 ^ 2 * H ^ 14 +
    (54975581388800 : K[X]) * a2 * a3 * a5 * H ^ 14 +
    (65970697666560 : K[X]) * a2 * a4 ^ 2 * H ^ 14 +
    (65970697666560 : K[X]) * a3 ^ 2 * a4 * H ^ 14 -
    (52776558133248 : K[X]) * a0 * b6 * a6 * H ^ 13 +
    (39582418599936 : K[X]) * a0 * b6 * g2 ^ 2 * H ^ 13 -
    (52776558133248 : K[X]) * a1 * a5 * b6 * H ^ 13 -
    (43980465111040 : K[X]) * a1 * b5 * a6 * H ^ 13 +
    (32985348833280 : K[X]) * a1 * b5 * g2 ^ 2 * H ^ 13 -
    (52776558133248 : K[X]) * a2 * a4 * b6 * H ^ 13 -
    (43980465111040 : K[X]) * a2 * a5 * b5 * H ^ 13 -
    (35184372088832 : K[X]) * a2 * b4 * a6 * H ^ 13 +
    (26388279066624 : K[X]) * a2 * b4 * g2 ^ 2 * H ^ 13 -
    (26388279066624 : K[X]) * a3 ^ 2 * b6 * H ^ 13 -
    (43980465111040 : K[X]) * a3 * a4 * b5 * H ^ 13 -
    (35184372088832 : K[X]) * a3 * a5 * b4 * H ^ 13 -
    (26388279066624 : K[X]) * a3 * b3 * a6 * H ^ 13 +
    (19791209299968 : K[X]) * a3 * b3 * g2 ^ 2 * H ^ 13 -
    (17592186044416 : K[X]) * a4 ^ 2 * b4 * H ^ 13 -
    (26388279066624 : K[X]) * a4 * a5 * b3 * H ^ 13 -
    (17592186044416 : K[X]) * a4 * b2 * a6 * H ^ 13 +
    (13194139533312 : K[X]) * a4 * b2 * g2 ^ 2 * H ^ 13 -
    (8796093022208 : K[X]) * a5 ^ 2 * b2 * H ^ 13 -
    (8796093022208 : K[X]) * a5 * b1 * a6 * H ^ 13 +
    (6597069766656 : K[X]) * a5 * b1 * g2 ^ 2 * H ^ 13 +
    (46729244180480 : K[X]) * a0 * a5 * a6 * g2 * H ^ 12 -
    (22333829939200 : K[X]) * a0 * a5 * g2 ^ 3 * H ^ 12 -
    (68719476736000 : K[X]) * a1 * a4 * a6 * g2 * H ^ 12 +
    (25769803776000 : K[X]) * a1 * a4 * g2 ^ 3 * H ^ 12 +
    (24739011624960 : K[X]) * a1 * a5 ^ 2 * g2 * H ^ 12 -
    (68719476736000 : K[X]) * a2 * a3 * a6 * g2 * H ^ 12 +
    (25769803776000 : K[X]) * a2 * a3 * g2 ^ 3 * H ^ 12 -
    (65970697666560 : K[X]) * a2 * a4 * a5 * g2 * H ^ 12 -
    (32985348833280 : K[X]) * a3 ^ 2 * a5 * g2 * H ^ 12 -
    (90709709291520 : K[X]) * a3 * a4 ^ 2 * g2 * H ^ 12 +
    (79164837199872 : K[X]) * a1 * b6 * a6 * g2 * H ^ 11 -
    (32985348833280 : K[X]) * a1 * b6 * g2 ^ 3 * H ^ 11 +
    (79164837199872 : K[X]) * a2 * a5 * b6 * g2 * H ^ 11 +
    (65970697666560 : K[X]) * a2 * b5 * a6 * g2 * H ^ 11 -
    (27487790694400 : K[X]) * a2 * b5 * g2 ^ 3 * H ^ 11 +
    (79164837199872 : K[X]) * a3 * a4 * b6 * g2 * H ^ 11 +
    (65970697666560 : K[X]) * a3 * a5 * b5 * g2 * H ^ 11 +
    (52776558133248 : K[X]) * a3 * b4 * a6 * g2 * H ^ 11 -
    (21990232555520 : K[X]) * a3 * b4 * g2 ^ 3 * H ^ 11 +
    (32985348833280 : K[X]) * a4 ^ 2 * b5 * g2 * H ^ 11 +
    (52776558133248 : K[X]) * a4 * a5 * b4 * g2 * H ^ 11 +
    (39582418599936 : K[X]) * a4 * b3 * a6 * g2 * H ^ 11 -
    (16492674416640 : K[X]) * a4 * b3 * g2 ^ 3 * H ^ 11 +
    (19791209299968 : K[X]) * a5 ^ 2 * b3 * g2 * H ^ 11 +
    (26388279066624 : K[X]) * a5 * b2 * a6 * g2 * H ^ 11 -
    (10995116277760 : K[X]) * a5 * b2 * g2 ^ 3 * H ^ 11 +
    (6597069766656 : K[X]) * b1 * a6 ^ 2 * g2 * H ^ 11 -
    (5497558138880 : K[X]) * b1 * a6 * g2 ^ 3 * H ^ 11 +
    (962072674304 : K[X]) * b1 * g2 ^ 5 * H ^ 11 +
    (10995116277760 : K[X]) * a0 * a6 ^ 3 * H ^ 10 -
    (24739011624960 : K[X]) * a0 * a6 ^ 2 * g2 ^ 2 * H ^ 10 +
    (11854109736960 : K[X]) * a0 * a6 * g2 ^ 4 * H ^ 10 -
    (1503238553600 : K[X]) * a0 * g2 ^ 6 * H ^ 10 +
    (24739011624960 : K[X]) * a1 * a5 * a6 ^ 2 * H ^ 10 -
    (57724360458240 : K[X]) * a1 * a5 * a6 * g2 ^ 2 * H ^ 10 +
    (17867063951360 : K[X]) * a1 * a5 * g2 ^ 4 * H ^ 10 -
    (32985348833280 : K[X]) * a2 * a4 * a6 ^ 2 * H ^ 10 +
    (86586540687360 : K[X]) * a2 * a4 * a6 * g2 ^ 2 * H ^ 10 -
    (24223615549440 : K[X]) * a2 * a4 * g2 ^ 4 * H ^ 10 +
    (16492674416640 : K[X]) * a2 * a5 ^ 2 * a6 * H ^ 10 -
    (32985348833280 : K[X]) * a2 * a5 ^ 2 * g2 ^ 2 * H ^ 10 -
    (16492674416640 : K[X]) * a3 ^ 2 * a6 ^ 2 * H ^ 10 +
    (43293270343680 : K[X]) * a3 ^ 2 * a6 * g2 ^ 2 * H ^ 10 -
    (12111807774720 : K[X]) * a3 ^ 2 * g2 ^ 4 * H ^ 10 -
    (82463372083200 : K[X]) * a3 * a4 * a5 * a6 * H ^ 10 +
    (78340203479040 : K[X]) * a3 * a4 * a5 * g2 ^ 2 * H ^ 10 +
    (2748779069440 : K[X]) * a3 * a5 ^ 3 * H ^ 10 -
    (32985348833280 : K[X]) * a4 ^ 3 * a6 * H ^ 10 +
    (37108517437440 : K[X]) * a4 ^ 3 * g2 ^ 2 * H ^ 10 -
    (24739011624960 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 10 +
    (39582418599936 : K[X]) * a2 * b6 * a6 ^ 2 * H ^ 9 -
    (98956046499840 : K[X]) * a2 * b6 * a6 * g2 ^ 2 * H ^ 9 +
    (28862180229120 : K[X]) * a2 * b6 * g2 ^ 4 * H ^ 9 +
    (79164837199872 : K[X]) * a3 * a5 * b6 * a6 * H ^ 9 -
    (98956046499840 : K[X]) * a3 * a5 * b6 * g2 ^ 2 * H ^ 9 +
    (32985348833280 : K[X]) * a3 * b5 * a6 ^ 2 * H ^ 9 -
    (82463372083200 : K[X]) * a3 * b5 * a6 * g2 ^ 2 * H ^ 9 +
    (24051816857600 : K[X]) * a3 * b5 * g2 ^ 4 * H ^ 9 +
    (39582418599936 : K[X]) * a4 ^ 2 * b6 * a6 * H ^ 9 -
    (49478023249920 : K[X]) * a4 ^ 2 * b6 * g2 ^ 2 * H ^ 9 +
    (39582418599936 : K[X]) * a4 * a5 ^ 2 * b6 * H ^ 9 +
    (65970697666560 : K[X]) * a4 * a5 * b5 * a6 * H ^ 9 -
    (82463372083200 : K[X]) * a4 * a5 * b5 * g2 ^ 2 * H ^ 9 +
    (26388279066624 : K[X]) * a4 * b4 * a6 ^ 2 * H ^ 9 -
    (65970697666560 : K[X]) * a4 * b4 * a6 * g2 ^ 2 * H ^ 9 +
    (19241453486080 : K[X]) * a4 * b4 * g2 ^ 4 * H ^ 9 +
    (10995116277760 : K[X]) * a5 ^ 3 * b5 * H ^ 9 +
    (26388279066624 : K[X]) * a5 ^ 2 * b4 * a6 * H ^ 9 -
    (32985348833280 : K[X]) * a5 ^ 2 * b4 * g2 ^ 2 * H ^ 9 +
    (19791209299968 : K[X]) * a5 * b3 * a6 ^ 2 * H ^ 9 -
    (49478023249920 : K[X]) * a5 * b3 * a6 * g2 ^ 2 * H ^ 9 +
    (14431090114560 : K[X]) * a5 * b3 * g2 ^ 4 * H ^ 9 +
    (4398046511104 : K[X]) * b2 * a6 ^ 3 * H ^ 9 -
    (16492674416640 : K[X]) * b2 * a6 ^ 2 * g2 ^ 2 * H ^ 9 +
    (9620726743040 : K[X]) * b2 * a6 * g2 ^ 4 * H ^ 9 -
    (1443109011456 : K[X]) * b2 * g2 ^ 6 * H ^ 9 -
    (19928648253440 : K[X]) * a1 * a6 ^ 3 * g2 * H ^ 8 +
    (25683904430080 : K[X]) * a1 * a6 ^ 2 * g2 ^ 3 * H ^ 8 -
    (9620726743040 : K[X]) * a1 * a6 * g2 ^ 5 * H ^ 8 +
    (1068373114880 : K[X]) * a1 * g2 ^ 7 * H ^ 8 -
    (53601191854080 : K[X]) * a2 * a5 * a6 ^ 2 * g2 * H ^ 8 +
    (63393717288960 : K[X]) * a2 * a5 * a6 * g2 ^ 3 * H ^ 8 -
    (14731737825280 : K[X]) * a2 * a5 * g2 ^ 5 * H ^ 8 +
    (90709709291520 : K[X]) * a3 * a4 * a6 ^ 2 * g2 * H ^ 8 -
    (104969000714240 : K[X]) * a3 * a4 * a6 * g2 ^ 3 * H ^ 8 +
    (23149873725440 : K[X]) * a3 * a4 * g2 ^ 5 * H ^ 8 -
    (47416438947840 : K[X]) * a3 * a5 ^ 2 * a6 * g2 * H ^ 8 +
    (37709812858880 : K[X]) * a3 * a5 ^ 2 * g2 ^ 3 * H ^ 8 +
    (96894462197760 : K[X]) * a4 ^ 2 * a5 * a6 * g2 * H ^ 8 -
    (46471546142720 : K[X]) * a4 ^ 2 * a5 * g2 ^ 3 * H ^ 8 -
    (13743895347200 : K[X]) * a4 * a5 ^ 3 * g2 * H ^ 8 -
    (98956046499840 : K[X]) * a3 * b6 * a6 ^ 2 * g2 * H ^ 7 +
    (115448720916480 : K[X]) * a3 * b6 * a6 * g2 ^ 3 * H ^ 7 -
    (25975962206208 : K[X]) * a3 * b6 * g2 ^ 5 * H ^ 7 -
    (197912092999680 : K[X]) * a4 * a5 * b6 * a6 * g2 * H ^ 7 +
    (115448720916480 : K[X]) * a4 * a5 * b6 * g2 ^ 3 * H ^ 7 -
    (82463372083200 : K[X]) * a4 * b5 * a6 ^ 2 * g2 * H ^ 7 +
    (96207267430400 : K[X]) * a4 * b5 * a6 * g2 ^ 3 * H ^ 7 -
    (21646635171840 : K[X]) * a4 * b5 * g2 ^ 5 * H ^ 7 -
    (32985348833280 : K[X]) * a5 ^ 3 * b6 * g2 * H ^ 7 -
    (82463372083200 : K[X]) * a5 ^ 2 * b5 * a6 * g2 * H ^ 7 +
    (48103633715200 : K[X]) * a5 ^ 2 * b5 * g2 ^ 3 * H ^ 7 -
    (65970697666560 : K[X]) * a5 * b4 * a6 ^ 2 * g2 * H ^ 7 +
    (76965813944320 : K[X]) * a5 * b4 * a6 * g2 ^ 3 * H ^ 7 -
    (17317308137472 : K[X]) * a5 * b4 * g2 ^ 5 * H ^ 7 -
    (16492674416640 : K[X]) * b3 * a6 ^ 3 * g2 * H ^ 7 +
    (28862180229120 : K[X]) * b3 * a6 ^ 2 * g2 ^ 3 * H ^ 7 -
    (12987981103104 : K[X]) * b3 * a6 * g2 ^ 5 * H ^ 7 +
    (1700807049216 : K[X]) * b3 * g2 ^ 7 * H ^ 7 -
    (6871947673600 : K[X]) * a2 * a6 ^ 4 * H ^ 6 +
    (29205777612800 : K[X]) * a2 * a6 ^ 3 * g2 ^ 2 * H ^ 6 -
    (25555055411200 : K[X]) * a2 * a6 ^ 2 * g2 ^ 4 * H ^ 6 +
    (7816840478720 : K[X]) * a2 * a6 * g2 ^ 6 * H ^ 6 -
    (765041049600 : K[X]) * a2 * g2 ^ 8 * H ^ 6 -
    (20615843020800 : K[X]) * a3 * a5 * a6 ^ 3 * H ^ 6 +
    (87617332838400 : K[X]) * a3 * a5 * a6 ^ 2 * g2 ^ 2 * H ^ 6 -
    (66142496358400 : K[X]) * a3 * a5 * a6 * g2 ^ 4 * H ^ 6 +
    (12326556139520 : K[X]) * a3 * a5 * g2 ^ 6 * H ^ 6 +
    (13743895347200 : K[X]) * a4 ^ 2 * a6 ^ 3 * H ^ 6 -
    (82463372083200 : K[X]) * a4 ^ 2 * a6 ^ 2 * g2 ^ 2 * H ^ 6 +
    (61632780697600 : K[X]) * a4 ^ 2 * a6 * g2 ^ 4 * H ^ 6 -
    (11199127224320 : K[X]) * a4 ^ 2 * g2 ^ 6 * H ^ 6 -
    (20615843020800 : K[X]) * a4 * a5 ^ 2 * a6 ^ 2 * H ^ 6 +
    (87617332838400 : K[X]) * a4 * a5 ^ 2 * a6 * g2 ^ 2 * H ^ 6 -
    (40587440947200 : K[X]) * a4 * a5 ^ 2 * g2 ^ 4 * H ^ 6 -
    (13743895347200 : K[X]) * a5 ^ 4 * a6 * H ^ 6 +
    (28346784153600 : K[X]) * a5 ^ 4 * g2 ^ 2 * H ^ 6 -
    (32985348833280 : K[X]) * a4 * b6 * a6 ^ 3 * H ^ 5 +
    (173173081374720 : K[X]) * a4 * b6 * a6 ^ 2 * g2 ^ 2 * H ^ 5 -
    (129879811031040 : K[X]) * a4 * b6 * a6 * g2 ^ 4 * H ^ 5 +
    (23811298689024 : K[X]) * a4 * b6 * g2 ^ 6 * H ^ 5 -
    (49478023249920 : K[X]) * a5 ^ 2 * b6 * a6 ^ 2 * H ^ 5 +
    (173173081374720 : K[X]) * a5 ^ 2 * b6 * a6 * g2 ^ 2 * H ^ 5 -
    (64939905515520 : K[X]) * a5 ^ 2 * b6 * g2 ^ 4 * H ^ 5 -
    (27487790694400 : K[X]) * a5 * b5 * a6 ^ 3 * H ^ 5 +
    (144310901145600 : K[X]) * a5 * b5 * a6 ^ 2 * g2 ^ 2 * H ^ 5 -
    (108233175859200 : K[X]) * a5 * b5 * a6 * g2 ^ 4 * H ^ 5 +
    (19842748907520 : K[X]) * a5 * b5 * g2 ^ 6 * H ^ 5 -
    (5497558138880 : K[X]) * b4 * a6 ^ 4 * H ^ 5 +
    (38482906972160 : K[X]) * b4 * a6 ^ 3 * g2 ^ 2 * H ^ 5 -
    (43293270343680 : K[X]) * b4 * a6 ^ 2 * g2 ^ 4 * H ^ 5 +
    (15874199126016 : K[X]) * b4 * a6 * g2 ^ 6 * H ^ 5 -
    (1842540969984 : K[X]) * b4 * g2 ^ 8 * H ^ 5 +
    (18038862643200 : K[X]) * a3 * a6 ^ 4 * g2 * H ^ 4 -
    (37580963840000 : K[X]) * a3 * a6 ^ 3 * g2 ^ 3 * H ^ 4 +
    (24577950351360 : K[X]) * a3 * a6 ^ 2 * g2 ^ 5 * H ^ 4 -
    (6305548861440 : K[X]) * a3 * a6 * g2 ^ 7 * H ^ 4 +
    (546266152960 : K[X]) * a3 * g2 ^ 9 * H ^ 4 +
    (60129542144000 : K[X]) * a4 * a5 * a6 ^ 3 * g2 * H ^ 4 -
    (121762322841600 : K[X]) * a4 * a5 * a6 ^ 2 * g2 ^ 3 * H ^ 4 +
    (66743791779840 : K[X]) * a4 * a5 * a6 * g2 ^ 5 * H ^ 4 -
    (10380399083520 : K[X]) * a4 * a5 * g2 ^ 7 * H ^ 4 +
    (108233175859200 : K[X]) * a5 ^ 3 * a6 ^ 2 * g2 * H ^ 4 -
    (169865956556800 : K[X]) * a5 ^ 3 * a6 * g2 ^ 3 * H ^ 4 +
    (48780091064320 : K[X]) * a5 ^ 3 * g2 ^ 5 * H ^ 4 +
    (115448720916480 : K[X]) * a5 * b6 * a6 ^ 3 * g2 * H ^ 3 -
    (259759622062080 : K[X]) * a5 * b6 * a6 ^ 2 * g2 ^ 3 * H ^ 3 +
    (142867792134144 : K[X]) * a5 * b6 * a6 * g2 ^ 5 * H ^ 3 -
    (22110491639808 : K[X]) * a5 * b6 * g2 ^ 7 * H ^ 3 +
    (24051816857600 : K[X]) * b5 * a6 ^ 4 * g2 * H ^ 3 -
    (72155450572800 : K[X]) * b5 * a6 ^ 3 * g2 ^ 3 * H ^ 3 +
    (59528246722560 : K[X]) * b5 * a6 ^ 2 * g2 ^ 5 * H ^ 3 -
    (18425409699840 : K[X]) * b5 * a6 * g2 ^ 7 * H ^ 3 +
    (1919313510400 : K[X]) * b5 * g2 ^ 9 * H ^ 3 +
    (4810363371520 : K[X]) * a4 * a6 ^ 5 * H ^ 2 -
    (33071248179200 : K[X]) * a4 * a6 ^ 4 * g2 ^ 2 * H ^ 2 +
    (44345537331200 : K[X]) * a4 * a6 ^ 3 * g2 ^ 4 * H ^ 2 -
    (22886806978560 : K[X]) * a4 * a6 ^ 2 * g2 ^ 6 * H ^ 2 +
    (5004979077120 : K[X]) * a4 * a6 * g2 ^ 8 * H ^ 2 -
    (383862702080 : K[X]) * a4 * g2 ^ 10 * H ^ 2 +
    (30064771072000 : K[X]) * a5 ^ 2 * a6 ^ 4 * H ^ 2 -
    (249537599897600 : K[X]) * a5 ^ 2 * a6 ^ 3 * g2 ^ 2 * H ^ 2 +
    (337101245644800 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 ^ 4 * H ^ 2 -
    (145663815843840 : K[X]) * a5 ^ 2 * a6 * g2 ^ 6 * H ^ 2 +
    (19488414105600 : K[X]) * a5 ^ 2 * g2 ^ 8 * H ^ 2 +
    (5772436045824 : K[X]) * b6 * a6 ^ 5 * H -
    (64939905515520 : K[X]) * b6 * a6 ^ 4 * g2 ^ 2 * H +
    (119056493445120 : K[X]) * b6 * a6 ^ 3 * g2 ^ 4 * H -
    (77386720739328 : K[X]) * b6 * a6 ^ 2 * g2 ^ 6 * H +
    (20728585912320 : K[X]) * b6 * a6 * g2 ^ 8 * H -
    (1957699780608 : K[X]) * b6 * g2 ^ 10 * H -
    (54417235640320 : K[X]) * a5 * a6 ^ 5 * g2 +
    (224170449305600 : K[X]) * a5 * a6 ^ 4 * g2 ^ 3 -
    (274641683742720 : K[X]) * a5 * a6 ^ 3 * g2 ^ 5 +
    (141490315591680 : K[X]) * a5 * a6 ^ 2 * g2 ^ 7 -
    (32412406906880 : K[X]) * a5 * a6 * g2 ^ 9 +
    (2726024970240 : K[X]) * a5 * g2 ^ 11 +
    Polynomial.C κ *
      (-(2199023255552 : K[X]) * a0 * a4 * H ^ 17 -
        (2199023255552 : K[X]) * a1 * a3 * H ^ 17 -
        (1099511627776 : K[X]) * a2 ^ 2 * H ^ 17 +
        (1374389534720 : K[X]) * a0 * a5 * g2 * H ^ 15 +
        (1374389534720 : K[X]) * a1 * a4 * g2 * H ^ 15 +
        (1374389534720 : K[X]) * a2 * a3 * g2 * H ^ 15 +
        (1649267441664 : K[X]) * a0 * a6 ^ 2 * H ^ 13 -
        (1236950581248 : K[X]) * a0 * a6 * g2 ^ 2 * H ^ 13 +
        (3298534883328 : K[X]) * a1 * a5 * a6 * H ^ 13 -
        (1236950581248 : K[X]) * a1 * a5 * g2 ^ 2 * H ^ 13 +
        (3298534883328 : K[X]) * a2 * a4 * a6 * H ^ 13 -
        (1236950581248 : K[X]) * a2 * a4 * g2 ^ 2 * H ^ 13 +
        (1649267441664 : K[X]) * a2 * a5 ^ 2 * H ^ 13 +
        (1649267441664 : K[X]) * a3 ^ 2 * a6 * H ^ 13 -
        (618475290624 : K[X]) * a3 ^ 2 * g2 ^ 2 * H ^ 13 +
        (3298534883328 : K[X]) * a3 * a4 * a5 * H ^ 13 +
        (549755813888 : K[X]) * a4 ^ 3 * H ^ 13 -
        (2680059592704 : K[X]) * a1 * a6 ^ 2 * g2 * H ^ 11 +
        (1202590842880 : K[X]) * a1 * a6 * g2 ^ 3 * H ^ 11 -
        (30064771072 : K[X]) * a1 * g2 ^ 5 * H ^ 11 -
        (5360119185408 : K[X]) * a2 * a5 * a6 * g2 * H ^ 11 +
        (1202590842880 : K[X]) * a2 * a5 * g2 ^ 3 * H ^ 11 -
        (5360119185408 : K[X]) * a3 * a4 * a6 * g2 * H ^ 11 +
        (1202590842880 : K[X]) * a3 * a4 * g2 ^ 3 * H ^ 11 -
        (2680059592704 : K[X]) * a3 * a5 ^ 2 * g2 * H ^ 11 -
        (2680059592704 : K[X]) * a4 ^ 2 * a5 * g2 * H ^ 11 -
        (1374389534720 : K[X]) * a2 * a6 ^ 3 * H ^ 9 +
        (3607772528640 : K[X]) * a2 * a6 ^ 2 * g2 ^ 2 * H ^ 9 -
        (1202590842880 : K[X]) * a2 * a6 * g2 ^ 4 * H ^ 9 +
        (45097156608 : K[X]) * a2 * g2 ^ 6 * H ^ 9 -
        (4123168604160 : K[X]) * a3 * a5 * a6 ^ 2 * H ^ 9 +
        (7215545057280 : K[X]) * a3 * a5 * a6 * g2 ^ 2 * H ^ 9 -
        (1202590842880 : K[X]) * a3 * a5 * g2 ^ 4 * H ^ 9 -
        (2061584302080 : K[X]) * a4 ^ 2 * a6 ^ 2 * H ^ 9 +
        (3607772528640 : K[X]) * a4 ^ 2 * a6 * g2 ^ 2 * H ^ 9 -
        (601295421440 : K[X]) * a4 ^ 2 * g2 ^ 4 * H ^ 9 -
        (4123168604160 : K[X]) * a4 * a5 ^ 2 * a6 * H ^ 9 +
        (3607772528640 : K[X]) * a4 * a5 ^ 2 * g2 ^ 2 * H ^ 9 -
        (343597383680 : K[X]) * a5 ^ 4 * H ^ 9 +
        (3607772528640 : K[X]) * a3 * a6 ^ 3 * g2 * H ^ 7 -
        (4509715660800 : K[X]) * a3 * a6 ^ 2 * g2 ^ 3 * H ^ 7 +
        (1217623228416 : K[X]) * a3 * a6 * g2 ^ 5 * H ^ 7 -
        (53150220288 : K[X]) * a3 * g2 ^ 7 * H ^ 7 +
        (10823317585920 : K[X]) * a4 * a5 * a6 ^ 2 * g2 * H ^ 7 -
        (9019431321600 : K[X]) * a4 * a5 * a6 * g2 ^ 3 * H ^ 7 +
        (1217623228416 : K[X]) * a4 * a5 * g2 ^ 5 * H ^ 7 +
        (3607772528640 : K[X]) * a5 ^ 3 * a6 * g2 * H ^ 7 -
        (1503238553600 : K[X]) * a5 ^ 3 * g2 ^ 3 * H ^ 7 +
        (1202590842880 : K[X]) * a4 * a6 ^ 4 * H ^ 5 -
        (6614249635840 : K[X]) * a4 * a6 ^ 3 * g2 ^ 2 * H ^ 5 +
        (5411658792960 : K[X]) * a4 * a6 ^ 2 * g2 ^ 4 * H ^ 5 -
        (1240171806720 : K[X]) * a4 * a6 * g2 ^ 6 * H ^ 5 +
        (57579405312 : K[X]) * a4 * g2 ^ 8 * H ^ 5 +
        (2405181685760 : K[X]) * a5 ^ 2 * a6 ^ 3 * H ^ 5 -
        (9921374453760 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 ^ 2 * H ^ 5 +
        (5411658792960 : K[X]) * a5 ^ 2 * a6 * g2 ^ 4 * H ^ 5 -
        (620085903360 : K[X]) * a5 ^ 2 * g2 ^ 6 * H ^ 5 -
        (4359391805440 : K[X]) * a5 * a6 ^ 4 * g2 * H ^ 3 +
        (10372346019840 : K[X]) * a5 * a6 ^ 3 * g2 ^ 3 * H ^ 3 -
        (6324876214272 : K[X]) * a5 * a6 ^ 2 * g2 ^ 5 * H ^ 3 +
        (1266746916864 : K[X]) * a5 * a6 * g2 ^ 7 * H ^ 3 -
        (59978547200 : K[X]) * a5 * g2 ^ 9 * H ^ 3 -
        (180388626432 : K[X]) * a6 ^ 6 * H +
        (2029372047360 : K[X]) * a6 ^ 5 * g2 ^ 2 * H -
        (3720515420160 : K[X]) * a6 ^ 4 * g2 ^ 4 * H +
        (2418335023104 : K[X]) * a6 ^ 3 * g2 ^ 6 * H -
        (647768309760 : K[X]) * a6 ^ 2 * g2 ^ 8 * H +
        (61178118144 : K[X]) * a6 * g2 ^ 10 * H)

/-- Cleared fourteenth row of the nonsquare chamber, in factored form:
`H²` times the transport co-factor plus the split `g₂, p₆` block
`2621440 (g₂² - 4 p₆)` times the even dodecic. -/
def alignedFourteenthNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedFourteenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2
        b3 b4 b5 b6 κ +
    (2621440 : K[X]) * (g2 ^ 2 - (4 : K[X]) * a6) *
      ((46189 : K[X]) * g2 ^ 12 - (583440 : K[X]) * a6 * g2 ^ 10 +
        (2759328 : K[X]) * a6 ^ 2 * g2 ^ 8 -
        (6040320 : K[X]) * a6 ^ 3 * g2 ^ 6 +
        (6057216 : K[X]) * a6 ^ 4 * g2 ^ 4 -
        (2285568 : K[X]) * a6 ^ 5 * g2 ^ 2 +
        (147456 : K[X]) * a6 ^ 6)

/-! ## Square chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀⁵⁶` from `N₁₄ = κ₁₃ H⁴⁹` on `H = h₀²`, `p₇ = h₀⁴ g₁`
and consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `-481036337152 p₀ p₅ h₀²⁸
- 481036337152 p₁ p₄ h₀²⁸ - 481036337152 p₂ p₃ h₀²⁸
+ 721554505728 p₀ p₆ g₁ h₀²⁴ - 300647710720 p₀ g₁³ h₀²⁴
+ 721554505728 p₁ p₅ g₁ h₀²⁴ + 721554505728 p₂ p₄ g₁ h₀²⁴
+ 360777252864 p₃² g₁ h₀²⁴ + … + 15410397184 g₁¹¹`, leaves the cleared
fourteenth row of the square chamber together with its factored
transport form.  Nothing is forced: `κ₁₃` is preserved, not
cleared. -/
theorem alignedSquareFourteenth_solved_810 {K : Type*} [Field K]
    [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₃ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hN : alignedFourteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₁₃ * H ^ 49)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedFourteenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
        b5 b6 κ μ =
      Polynomial.C κ₁₃ * h0 ^ 42 ∧
    (2621440 : K[X]) * (g1 ^ 2 - (4 : K[X]) * a6) *
        ((46189 : K[X]) * g1 ^ 12 - (583440 : K[X]) * a6 * g1 ^ 10 +
          (2759328 : K[X]) * a6 ^ 2 * g1 ^ 8 -
          (6040320 : K[X]) * a6 ^ 3 * g1 ^ 6 +
          (6057216 : K[X]) * a6 ^ 4 * g1 ^ 4 -
          (2285568 : K[X]) * a6 ^ 5 * g1 ^ 2 +
          (147456 : K[X]) * a6 ^ 6) =
      h0 ^ 4 *
        (Polynomial.C κ₁₃ * h0 ^ 38 -
          alignedFourteenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2
            b3 b4 b5 b6 κ μ) := by
  have hN' := hN
  simp only [alignedFourteenthDefect810, hHsq, hg] at hN'
  have hclear :
      alignedFourteenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ μ =
        Polynomial.C κ₁₃ * h0 ^ 42 := by
    simp only [alignedFourteenthSquareRow810, alignedFourteenthSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 56 hh0)
    linear_combination hN' -
      h0 ^ 56 *
        (-(481036337152 : K[X]) * a0 * a5 * h0 ^ 28 -
          (481036337152 : K[X]) * a1 * a4 * h0 ^ 28 -
          (481036337152 : K[X]) * a2 * a3 * h0 ^ 28 +
          (721554505728 : K[X]) * a0 * a6 * g1 * h0 ^ 24 -
          (300647710720 : K[X]) * a0 * g1 ^ 3 * h0 ^ 24 +
          (721554505728 : K[X]) * a1 * a5 * g1 * h0 ^ 24 +
          (721554505728 : K[X]) * a2 * a4 * g1 * h0 ^ 24 +
          (360777252864 : K[X]) * a3 ^ 2 * g1 * h0 ^ 24 +
          (360777252864 : K[X]) * a1 * a6 ^ 2 * h0 ^ 20 -
          (901943132160 : K[X]) * a1 * a6 * g1 ^ 2 * h0 ^ 20 +
          (263066746880 : K[X]) * a1 * g1 ^ 4 * h0 ^ 20 +
          (721554505728 : K[X]) * a2 * a5 * a6 * h0 ^ 20 -
          (901943132160 : K[X]) * a2 * a5 * g1 ^ 2 * h0 ^ 20 +
          (721554505728 : K[X]) * a3 * a4 * a6 * h0 ^ 20 -
          (901943132160 : K[X]) * a3 * a4 * g1 ^ 2 * h0 ^ 20 +
          (360777252864 : K[X]) * a3 * a5 ^ 2 * h0 ^ 20 +
          (360777252864 : K[X]) * a4 ^ 2 * a5 * h0 ^ 20 -
          (901943132160 : K[X]) * a2 * a6 ^ 2 * g1 * h0 ^ 16 +
          (1052266987520 : K[X]) * a2 * a6 * g1 ^ 3 * h0 ^ 16 -
          (236760072192 : K[X]) * a2 * g1 ^ 5 * h0 ^ 16 -
          (1803886264320 : K[X]) * a3 * a5 * a6 * g1 * h0 ^ 16 +
          (1052266987520 : K[X]) * a3 * a5 * g1 ^ 3 * h0 ^ 16 -
          (901943132160 : K[X]) * a4 ^ 2 * a6 * g1 * h0 ^ 16 +
          (526133493760 : K[X]) * a4 ^ 2 * g1 ^ 3 * h0 ^ 16 -
          (901943132160 : K[X]) * a4 * a5 ^ 2 * g1 * h0 ^ 16 -
          (300647710720 : K[X]) * a3 * a6 ^ 3 * h0 ^ 12 +
          (1578400481280 : K[X]) * a3 * a6 ^ 2 * g1 ^ 2 * h0 ^ 12 -
          (1183800360960 : K[X]) * a3 * a6 * g1 ^ 4 * h0 ^ 12 +
          (217030066176 : K[X]) * a3 * g1 ^ 6 * h0 ^ 12 -
          (901943132160 : K[X]) * a4 * a5 * a6 ^ 2 * h0 ^ 12 +
          (3156800962560 : K[X]) * a4 * a5 * a6 * g1 ^ 2 * h0 ^ 12 -
          (1183800360960 : K[X]) * a4 * a5 * g1 ^ 4 * h0 ^ 12 -
          (300647710720 : K[X]) * a5 ^ 3 * a6 * h0 ^ 12 +
          (526133493760 : K[X]) * a5 ^ 3 * g1 ^ 2 * h0 ^ 12 +
          (1052266987520 : K[X]) * a4 * a6 ^ 3 * g1 * h0 ^ 8 -
          (2367600721920 : K[X]) * a4 * a6 ^ 2 * g1 ^ 3 * h0 ^ 8 +
          (1302180397056 : K[X]) * a4 * a6 * g1 ^ 5 * h0 ^ 8 -
          (201527918592 : K[X]) * a4 * g1 ^ 7 * h0 ^ 8 +
          (1578400481280 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 * h0 ^ 8 -
          (2367600721920 : K[X]) * a5 ^ 2 * a6 * g1 ^ 3 * h0 ^ 8 +
          (651090198528 : K[X]) * a5 ^ 2 * g1 ^ 5 * h0 ^ 8 +
          (263066746880 : K[X]) * a5 * a6 ^ 4 * h0 ^ 4 -
          (2367600721920 : K[X]) * a5 * a6 ^ 3 * g1 ^ 2 * h0 ^ 4 +
          (3255450992640 : K[X]) * a5 * a6 ^ 2 * g1 ^ 4 * h0 ^ 4 -
          (1410695430144 : K[X]) * a5 * a6 * g1 ^ 6 * h0 ^ 4 +
          (188932423680 : K[X]) * a5 * g1 ^ 8 * h0 ^ 4 -
          (236760072192 : K[X]) * a6 ^ 5 * g1 +
          (1085150330880 : K[X]) * a6 ^ 4 * g1 ^ 3 -
          (1410695430144 : K[X]) * a6 ^ 3 * g1 ^ 5 +
          (755729694720 : K[X]) * a6 ^ 2 * g1 ^ 7 -
          (178436177920 : K[X]) * a6 * g1 ^ 9 +
          (15410397184 : K[X]) * g1 ^ 11) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedFourteenthSquareRow810] at hclear
  linear_combination hclear

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `H²⁸` from `N₁₄ = κ₁₃ H⁴⁹` on `p₇ = H² g₂` and consuming
the previous factored quotient (`128 q₇ H` solved) with the same mate,
leaves the cleared fourteenth row of the nonsquare chamber together
with its factored transport form.  The unsquared integral forces
nothing: `κ₁₃` is preserved, not cleared. -/
theorem alignedNonsquareFourteenth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₃ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hN : alignedFourteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₁₃ * H ^ 49)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedFourteenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ =
      Polynomial.C κ₁₃ * H ^ 21 ∧
    (2621440 : K[X]) * (g2 ^ 2 - (4 : K[X]) * a6) *
        ((46189 : K[X]) * g2 ^ 12 - (583440 : K[X]) * a6 * g2 ^ 10 +
          (2759328 : K[X]) * a6 ^ 2 * g2 ^ 8 -
          (6040320 : K[X]) * a6 ^ 3 * g2 ^ 6 +
          (6057216 : K[X]) * a6 ^ 4 * g2 ^ 4 -
          (2285568 : K[X]) * a6 ^ 5 * g2 ^ 2 +
          (147456 : K[X]) * a6 ^ 6) =
      H ^ 2 *
        (Polynomial.C κ₁₃ * H ^ 19 -
          alignedFourteenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1
            b2 b3 b4 b5 b6 κ) := by
  have hN' := hN
  simp only [alignedFourteenthDefect810, hg2] at hN'
  have hclear :
      alignedFourteenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ =
        Polynomial.C κ₁₃ * H ^ 21 := by
    simp only [alignedFourteenthNonsquareRow810,
      alignedFourteenthNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 28 hH)
    linear_combination hN' -
      H ^ 28 *
        (-(481036337152 : K[X]) * a0 * a5 * H ^ 14 -
          (481036337152 : K[X]) * a1 * a4 * H ^ 14 -
          (481036337152 : K[X]) * a2 * a3 * H ^ 14 +
          (721554505728 : K[X]) * a0 * a6 * g2 * H ^ 12 -
          (300647710720 : K[X]) * a0 * g2 ^ 3 * H ^ 12 +
          (721554505728 : K[X]) * a1 * a5 * g2 * H ^ 12 +
          (721554505728 : K[X]) * a2 * a4 * g2 * H ^ 12 +
          (360777252864 : K[X]) * a3 ^ 2 * g2 * H ^ 12 +
          (360777252864 : K[X]) * a1 * a6 ^ 2 * H ^ 10 -
          (901943132160 : K[X]) * a1 * a6 * g2 ^ 2 * H ^ 10 +
          (263066746880 : K[X]) * a1 * g2 ^ 4 * H ^ 10 +
          (721554505728 : K[X]) * a2 * a5 * a6 * H ^ 10 -
          (901943132160 : K[X]) * a2 * a5 * g2 ^ 2 * H ^ 10 +
          (721554505728 : K[X]) * a3 * a4 * a6 * H ^ 10 -
          (901943132160 : K[X]) * a3 * a4 * g2 ^ 2 * H ^ 10 +
          (360777252864 : K[X]) * a3 * a5 ^ 2 * H ^ 10 +
          (360777252864 : K[X]) * a4 ^ 2 * a5 * H ^ 10 -
          (901943132160 : K[X]) * a2 * a6 ^ 2 * g2 * H ^ 8 +
          (1052266987520 : K[X]) * a2 * a6 * g2 ^ 3 * H ^ 8 -
          (236760072192 : K[X]) * a2 * g2 ^ 5 * H ^ 8 -
          (1803886264320 : K[X]) * a3 * a5 * a6 * g2 * H ^ 8 +
          (1052266987520 : K[X]) * a3 * a5 * g2 ^ 3 * H ^ 8 -
          (901943132160 : K[X]) * a4 ^ 2 * a6 * g2 * H ^ 8 +
          (526133493760 : K[X]) * a4 ^ 2 * g2 ^ 3 * H ^ 8 -
          (901943132160 : K[X]) * a4 * a5 ^ 2 * g2 * H ^ 8 -
          (300647710720 : K[X]) * a3 * a6 ^ 3 * H ^ 6 +
          (1578400481280 : K[X]) * a3 * a6 ^ 2 * g2 ^ 2 * H ^ 6 -
          (1183800360960 : K[X]) * a3 * a6 * g2 ^ 4 * H ^ 6 +
          (217030066176 : K[X]) * a3 * g2 ^ 6 * H ^ 6 -
          (901943132160 : K[X]) * a4 * a5 * a6 ^ 2 * H ^ 6 +
          (3156800962560 : K[X]) * a4 * a5 * a6 * g2 ^ 2 * H ^ 6 -
          (1183800360960 : K[X]) * a4 * a5 * g2 ^ 4 * H ^ 6 -
          (300647710720 : K[X]) * a5 ^ 3 * a6 * H ^ 6 +
          (526133493760 : K[X]) * a5 ^ 3 * g2 ^ 2 * H ^ 6 +
          (1052266987520 : K[X]) * a4 * a6 ^ 3 * g2 * H ^ 4 -
          (2367600721920 : K[X]) * a4 * a6 ^ 2 * g2 ^ 3 * H ^ 4 +
          (1302180397056 : K[X]) * a4 * a6 * g2 ^ 5 * H ^ 4 -
          (201527918592 : K[X]) * a4 * g2 ^ 7 * H ^ 4 +
          (1578400481280 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 * H ^ 4 -
          (2367600721920 : K[X]) * a5 ^ 2 * a6 * g2 ^ 3 * H ^ 4 +
          (651090198528 : K[X]) * a5 ^ 2 * g2 ^ 5 * H ^ 4 +
          (263066746880 : K[X]) * a5 * a6 ^ 4 * H ^ 2 -
          (2367600721920 : K[X]) * a5 * a6 ^ 3 * g2 ^ 2 * H ^ 2 +
          (3255450992640 : K[X]) * a5 * a6 ^ 2 * g2 ^ 4 * H ^ 2 -
          (1410695430144 : K[X]) * a5 * a6 * g2 ^ 6 * H ^ 2 +
          (188932423680 : K[X]) * a5 * g2 ^ 8 * H ^ 2 -
          (236760072192 : K[X]) * a6 ^ 5 * g2 +
          (1085150330880 : K[X]) * a6 ^ 4 * g2 ^ 3 -
          (1410695430144 : K[X]) * a6 ^ 3 * g2 ^ 5 +
          (755729694720 : K[X]) * a6 ^ 2 * g2 ^ 7 -
          (178436177920 : K[X]) * a6 * g2 ^ 9 +
          (15410397184 : K[X]) * g2 ^ 11) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedFourteenthNonsquareRow810] at hclear
  linear_combination hclear

/-! ## Source-facing fourteenth-row packets -/

/-- Source-facing weight-ninety-eight integral of a normalized aligned
scale-two `(8,10)` source: the degree-`3` row is consumed into
`N₁₄ = κ₁₃ H⁴⁹` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedFourteenthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ κ₁₂ κ₁₃ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 35 ∧
        alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 21 ∧
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₆ * H ^ 49 ∧
        alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 28 ∧
        alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 63 ∧
        alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 35 ∧
        alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₀ * H ^ 77 ∧
        alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 42 ∧
        alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₁₂ * H ^ 91 ∧
        alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₃ * H ^ 49 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₉, hN10⟩ :=
    alignedTenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₁₀, hN11⟩ :=
    alignedEleventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₁₁, hN12⟩ :=
    alignedTwelfthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₁₂, hN13⟩ :=
    alignedThirteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₁₃, hN14⟩ :=
    alignedFourteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀, κ₁₁, κ₁₂, κ₁₃,
    aligned_q9_solved_810 haligned, hM, hE4, hF2, hG, hI2, hJ, hL2,
    hN10, hN11, hN12, hN13, hN14⟩

/-- Exact square-chamber fourteenth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`3`
row gives the cleared fourteenth row (with `q₁, …, q₆` at `h₀³⁸`)
against the preserved `κ₁₃`, the carried root collapse `g₁ = p₆ = 0`,
and the carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedFourteenthFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₁₃ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        alignedFourteenthSquareRow810 h0 g1 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ μ =
          Polynomial.C κ₁₃ * h0 ^ 42 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₃ * H ^ 49 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨g, hg⟩ := alignedSquare_dvd_p7_810 hHsq hM
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hD⟩ := alignedSquareThird_sqrt_810 hh0 hHsq hD2
  have hEcore := alignedSquareThird_core_810 hh0 hHsq hg hD
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨g1, hg1, hcore, hfac⟩ :=
    alignedSquareThird_descent_810 hh0 hdeg1 hEcore
  have hp7 : p.coeff 7 = h0 ^ 4 * g1 := by rw [hg, hg1]; ring
  have hbranch : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∨ g1.eval a ^ 2 = 8 * (p.coeff 6).eval a := by
    intro a ha
    refine alignedThird_factored_rootBranch_810 hfac ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, ha,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore4 := alignedSquareFourth_core_810 hh0 hHsq hp7 hE4
  have hsolved4 := alignedSquareFourth_solved_810 hcore4 hcore
  have hcollapse : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedSquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hdvdg1 : h0 ∣ g1 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 g1 (-(d / c)) hdeg1
      hroot (hcollapse _ hroot).1
  have hdvdp6 : h0 ∣ p.coeff 6 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 6) (-(d / c))
      hdeg1 hroot (hcollapse _ hroot).2
  obtain ⟨κ₁₃, hNrel⟩ :=
    alignedFourteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hsolved14, _hfact14⟩ :=
    alignedSquareFourteenth_solved_810 hh0 hHsq hp7 hNrel hcore
  exact ⟨κ, μ, κ₁₃, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hsolved14,
    hcollapse, hdvdg1, hdvdp6, hNrel⟩

/-- Exact nonsquare-chamber fourteenth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂` and the previous
packet, the consumed degree-`3` row gives the cleared fourteenth row
(with `q₁, …, q₆` at `H¹⁹`) against the preserved `κ₁₃`, the carried
root collapse `g₂ = p₆ = 0` at every (simple) root of the core, and
the carried descents `H ∣ g₂`, `H ∣ p₆`.  The unsquared integral
forces nothing: `κ₁₃` is not cleared. -/
theorem normalized810ScaleTwo_alignedFourteenthFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₁₃ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        alignedFourteenthNonsquareRow810 H g2 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ =
          Polynomial.C κ₁₃ * H ^ 21 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedFourteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₃ * H ^ 49 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨g, hg⟩ := alignedNonsquare_dvd_p7_810 hHdegree hnsq hM
  obtain ⟨g2, hg2'⟩ := alignedNonsquare_dvd_g_810 hHdegree hnsq hH hg hM
  have hg2 : p.coeff 7 = H ^ 2 * g2 := by
    rw [hg, hg2']
    ring
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk2, hD0⟩ :=
    alignedNonsquareThird_defect_eq_zero_810 hH hHdegree hnsq hD2
  obtain ⟨_hpeel, hfac⟩ := alignedNonsquareThird_solved_810 hH hg2 hD0
  have hbranch : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∨ g2.eval a ^ 2 = 8 * (p.coeff 6).eval a := by
    intro a ha
    refine alignedThird_factored_rootBranch_810 hfac ?_
    rw [Polynomial.eval_mul, ha, zero_mul]
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore4 := alignedNonsquareFourth_core_810 hH hg2 hE4
  have hsolved4 := alignedNonsquareFourth_solved_810 hcore4 hfac
  have hcollapse : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedNonsquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero
      hHdegree hnsq ha
  have hdvdg2 : H ∣ g2 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).1)
  have hdvdp6 : H ∣ p.coeff 6 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).2)
  obtain ⟨κ₁₃, hNrel⟩ :=
    alignedFourteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hclear14, _hfact14⟩ :=
    alignedNonsquareFourteenth_solved_810 hH hg2 hNrel hfac
  exact ⟨κ, κ₁₃, g2, hg2, by rw [hq9, hg2]; ring, hclear14,
    hcollapse, hdvdg2, hdvdp6, hNrel⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`3`
aligned row, carrying the factored transport of the split
quattuordecic block.  Neither chamber is excluded, the constants `κ`,
`μ`, `κ₁₃` are preserved (nothing is forced by the unsquared
integral), and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedFourteenthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₁₃ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (2621440 : K[X]) * (g1 ^ 2 - (4 : K[X]) * p.coeff 6) *
              ((46189 : K[X]) * g1 ^ 12 -
                (583440 : K[X]) * p.coeff 6 * g1 ^ 10 +
                (2759328 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 8 -
                (6040320 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 6 +
                (6057216 : K[X]) * p.coeff 6 ^ 4 * g1 ^ 4 -
                (2285568 : K[X]) * p.coeff 6 ^ 5 * g1 ^ 2 +
                (147456 : K[X]) * p.coeff 6 ^ 6) =
            h0 ^ 4 *
              (Polynomial.C κ₁₃ * h0 ^ 38 -
                alignedFourteenthSquareCof810 h0 g1 (p.coeff 0)
                  (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
                  (p.coeff 5) (p.coeff 6) (q.coeff 1) (q.coeff 2)
                  (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
                  κ μ) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₁₃ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (2621440 : K[X]) * (g2 ^ 2 - (4 : K[X]) * p.coeff 6) *
              ((46189 : K[X]) * g2 ^ 12 -
                (583440 : K[X]) * p.coeff 6 * g2 ^ 10 +
                (2759328 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 8 -
                (6040320 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 6 +
                (6057216 : K[X]) * p.coeff 6 ^ 4 * g2 ^ 4 -
                (2285568 : K[X]) * p.coeff 6 ^ 5 * g2 ^ 2 +
                (147456 : K[X]) * p.coeff 6 ^ 6) =
            H ^ 2 *
              (Polynomial.C κ₁₃ * H ^ 19 -
                alignedFourteenthNonsquareCof810 H g2 (p.coeff 0)
                  (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
                  (p.coeff 5) (p.coeff 6) (q.coeff 1) (q.coeff 2)
                  (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
                  κ) ∧
          (∀ a : K, H.eval a = 0 →
            g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          H ∣ g2 ∧ H ∣ p.coeff 6) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized810ScaleTwo_alignedFourteenthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₁₃, g1, hp7, hq9, hsolved14,
      hcollapse, hdvdg1, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₁₃, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedFourteenthSquareRow810] at hsolved14
    linear_combination hsolved14
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedFourteenthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₁₃, g2, hp7, hq9, hclear14, hcollapse,
      hdvdg2, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, κ₁₃, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedFourteenthNonsquareRow810] at hclear14
    linear_combination hclear14

/-- Chamber-independent root jet after the consumed degree-`3` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its split quattuordecic content is
absorbed by the degree-`13` collapse
(`alignedFourteenth_rootQuattuordecic_absorbed_810`) — and no new
coefficient occurs, so the row re-ties `q₁, …, q₆` into the cleared
fourteenth row instead of killing anything new at the root. -/
theorem normalized810ScaleTwo_alignedFourteenthFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 7).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (p.coeff 6).eval a = 0 :=
  normalized810ScaleTwo_alignedThirteenthFace_rootJet hsource haligned

#print axioms alignedFourteenthCoefficientJacobianRow_810
#print axioms alignedFourteenthDefect_weightedDerivative_identity_810
#print axioms alignedFourteenthDefectRow_eq_zero_810
#print axioms alignedFourteenthDefectPowerRelation_810
#print axioms alignedFourteenth_factored_rootBranch_810
#print axioms alignedFourteenth_rootQuattuordecic_absorbed_810
#print axioms alignedSquareFourteenth_solved_810
#print axioms alignedNonsquareFourteenth_solved_810
#print axioms normalized810ScaleTwo_alignedFourteenthFace_packet
#print axioms normalized810ScaleTwo_alignedFourteenthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedFourteenthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedFourteenthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedFourteenthFace_rootJet

end Max11DegreeRoutes
