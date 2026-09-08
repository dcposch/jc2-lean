import Fable810ScaleTwoAlignedTenthFaceScratch

/-! # Eleventh aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedTenthFaceScratch` consumed the degree-`6`
aligned Keller row (the chambered `N₁₁² = κ₁₀ H⁷⁷`).  This file
consumes the next unused aligned row, the degree-`5` Jacobian
coefficient (internal names `alignedTwelfth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9`/`8`/`7`/`6` rows
`2 H D' - 21 D H' = 0`, `H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`,
`H G' - 21 G H' = 0`, `2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`,
`2 H L' - 63 L H' = 0`, `H N₁₀' - 35 N₁₀ H' = 0`,
`2 H N₁₁' - 77 N₁₁ H' = 0`, the degree-`5` row is the weighted
derivative of the weight-eighty-four defect

`N₁₂ = -2061584302080 p₀ p₄ H⁴⁰ - 2061584302080 p₁ p₃ H⁴⁰
  - 1030792151040 p₂² H⁴⁰ + 1649267441664 p₀ q₆ H³⁹
  + 1374389534720 p₁ q₅ H³⁹ + 1099511627776 p₂ q₄ H³⁹
  + 824633720832 p₃ q₃ H³⁹ + 549755813888 p₄ q₂ H³⁹
  + 274877906944 p₅ q₁ H³⁹ + … + 10013942400 p₇¹²
  + κ (-51539607552 p₀ p₆ H³⁹ - 51539607552 p₁ p₅ H³⁹
       - 51539607552 p₂ p₄ H³⁹ - 25769803776 p₃² H³⁹ + …
       - 3204461568 p₇¹⁰ H⁷)`

(the full two-hundred-two-term expression is the literal body of
`alignedTwelfthDefect810`; the defect is `q₀`-free — both
weight-eighty-four `q₀`-ansatz monomials `q₀ p₆ H³⁹` and `q₀ p₇² H³⁵`
solve to zero — and `q₀` enters the multiplier identity only through
the `N₁₀`-row correction `1536 p₆ H⁴ (H N₁₀' - 35 N₁₀ H')`), via the
exact multiplier identity

`274877906944 H⁴⁰ · row₅ = (H N₁₂' - 42 N₁₂ H')
  + (5637144576 p₀ p₇ H²⁸ + 5637144576 p₁ p₆ H²⁸ + 5637144576 p₂ p₅ H²⁸
     + 5637144576 p₃ p₄ H²⁸ - … - 1878415 p₇⁹) (2 H D' - 21 D H')
  + (805306368 p₀ H²⁸ + 603979776 p₁ p₇ H²⁴ + 603979776 p₂ p₆ H²⁴
     + 603979776 p₃ p₅ H²⁴ + … + 763776 p₇⁸) (H E' - 14 E H')
  + (50331648 p₁ H²⁴ + 31457280 p₂ p₇ H²⁰ + 31457280 p₃ p₆ H²⁰
     + 31457280 p₄ p₅ H²⁰ - … - 112860 p₇⁷) (2 H F' - 35 F H')
  + (25165824 p₂ H²⁰ + 12582912 p₃ p₇ H¹⁶ + 12582912 p₄ p₆ H¹⁶
     + 6291456 p₅² H¹⁶ - … + 114688 p₇⁶) (H G' - 21 G H')
  + (196608 p₃ H¹⁶ + 73728 p₄ p₇ H¹² + 73728 p₅ p₆ H¹² - 23040 p₅ p₇² H⁸
     - 23040 p₆² p₇ H⁸ + 12480 p₆ p₇³ H⁴ - 1638 p₇⁵) (2 H I' - 49 I H')
  + (49152 p₄ H¹² + 12288 p₅ p₇ H⁸ + 6144 p₆² H⁸ - 4608 p₆ p₇² H⁴
     + 672 p₇⁴) (H J' - 28 J H')
  + (1536 p₅ H⁸ + 192 p₆ p₇ H⁴ - 28 p₇³) (2 H L' - 63 L H')
  + 1536 p₆ H⁴ (H N₁₀' - 35 N₁₀ H')
  + 3 p₇ (2 H N₁₁' - 77 N₁₁ H')`.

The row sees only `q₀, …, q₆`, so — as on the previous face — no `N`-
and no `C`-correction occurs at all: every correction is a consumed
tower row, and for the first time *two* integral-tower rows (`N₁₀` and
`N₁₁`) correct simultaneously.  On the aligned face every right-hand
correction vanishes, so `H N₁₂' = 42 N₁₂ H'` and the weight-eighty-four
first integral

`N₁₂ = κ₁₁ H⁴²`

holds for a preserved constant `κ₁₁`.  The defect is unsquared, so —
exactly as for the degree-`13`, degree-`11`, degree-`9`, and
degree-`7` rows — the integral is **chamber-free**: neither chamber
forces anything, and `κ₁₁` is preserved in both.

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: peeling `h₀⁴⁸` and consuming
  the previous factored quotient (`128 q₇ h₀²` solved, transported by
  the mate `-11274289152 p₀ g₁ h₀²⁴ + 9865003008 p₁ g₁² h₀²⁰
  - 11274289152 p₁ p₆ h₀²⁰ - 11274289152 p₂ p₅ h₀²⁰
  - 11274289152 p₃ p₄ h₀²⁰ + … + 801115392 g₁⁹ - 7442620416 g₁⁷ p₆
  + 23154819072 g₁⁵ p₆² - 26846167040 g₁³ p₆³ + 8477736960 g₁ p₆⁴`)
  leaves the cleared twelfth row `alignedTwelfthSquareRow810` (with
  `q₁, …, q₆` re-tied at `h₀³⁶`) against `κ₁₁ h₀³⁶`, and the factored
  transport `7040 (853461 g₁¹² - 12270960 p₆ g₁¹⁰ + 67374912 p₆² g₁⁸
  - 175142912 p₆³ g₁⁶ + 214609920 p₆⁴ g₁⁴ - 103219200 p₆⁵ g₁²
  + 9175040 p₆⁶) = h₀⁴ (κ₁₁ h₀³² - co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): with
  `p₇ = H² g₂`, peeling `H²⁴` and consuming the previous factored
  quotient (same mate) leaves the cleared twelfth row
  `alignedTwelfthNonsquareRow810` (with `q₁, …, q₆` at `H¹⁸`) against
  `κ₁₁ H¹⁸` and the transport `7040 (853461 g₂¹² - 12270960 p₆ g₂¹⁰
  + 67374912 p₆² g₂⁸ - 175142912 p₆³ g₂⁶ + 214609920 p₆⁴ g₂⁴
  - 103219200 p₆⁵ g₂² + 9175040 p₆⁶) = H² (κ₁₁ H¹⁶ - co-factor)`.

At a root of the transport co-factor the honest root branch is the
root dodecic `853461 g¹² - 12270960 p₆ g¹⁰ + 67374912 p₆² g⁸
- 175142912 p₆³ g⁶ + 214609920 p₆⁴ g⁴ - 103219200 p₆⁵ g²
+ 9175040 p₆⁶ = 0` — no `g`-factor splits off, since the block is even
in `g` with a pure `p₆⁶` tail, exactly as for the degree-`7` decic.
Like the quartic through undecic of the previous rows it adds *no new*
root information: the consumed degree-`13` row already collapsed
`g(a) = 0 ∧ p₆(a) = 0` at every core root, and that collapse absorbs
the dodecic identically (`alignedTwelfth_rootDodecic_absorbed_810`).
The chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` —
the row re-ties `q₁, …, q₆` into the cleared twelfth row (at `h₀³⁶`,
resp. `H¹⁸`) without killing anything new at the root.

No closure is claimed.  Both chambers remain open, nothing new is
forced (the unsquared integral forces neither `κ₁₁ = 0` nor
`N₁₂ ≡ 0` anywhere), the constants `κ`, `μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆`,
`κ₇`, `κ₈`, `κ₉`, `κ₁₀`, and the new `κ₁₁` are preserved where not
previously forced (`κ₈ = 0`, `κ₁₀ = 0` remain forced in the nonsquare
chamber only, by the consumed degree-`8` and degree-`6` rows), the
zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`,
`κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`, `κ₇ = 0`, `κ₈ = 0` in the square
chamber, `κ₉ = 0`, `κ₁₀ = 0` in the square chamber, `κ₁₁ = 0`) are
not excluded as polynomial identities, the deepened quotients
`g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H` from the degree-`13` face are still
not re-cleared through the tower here, the root dodecic is recorded
but not excluded as an identity, and no individual vanishing of `p₀`,
`p₁`, `p₂`, `p₃`, `p₄`, `p₅`, `q₀`, `q₁`, `q₂`, `q₃`, `q₄`, `q₅`,
`q₆`, `q₇` is claimed.  The next unused Keller row on the aligned face
is the degree-`4` Jacobian coefficient (weight-ninety-one defect, odd
exponent, hence chambered).  No total-degree or twice-prime theorem is
used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal degree-`5` Keller coefficient on the aligned face -/

/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`5` Jacobian coefficient. -/
theorem alignedTwelfthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-! ## Aligned twelfth defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-eighty-four defect of the degree-`5` aligned `(8,10)` row.
On the aligned face it is a polynomial first integral of even weight
eighty-four, hence chamber-free.  The defect is `q₀`-free. -/
def alignedTwelfthDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    K[X] :=
    -(2061584302080 : K[X]) * a0 * a4 * H ^ 40 -
    (2061584302080 : K[X]) * a1 * a3 * H ^ 40 -
    (1030792151040 : K[X]) * a2 ^ 2 * H ^ 40 +
    (1649267441664 : K[X]) * a0 * b6 * H ^ 39 +
    (1374389534720 : K[X]) * a1 * b5 * H ^ 39 +
    (1099511627776 : K[X]) * a2 * b4 * H ^ 39 +
    (824633720832 : K[X]) * a3 * b3 * H ^ 39 +
    (549755813888 : K[X]) * a4 * b2 * H ^ 39 +
    (274877906944 : K[X]) * a5 * b1 * H ^ 39 +
    (1288490188800 : K[X]) * a0 * a5 * a7 * H ^ 36 -
    (257698037760 : K[X]) * a0 * a6 ^ 2 * H ^ 36 +
    (1288490188800 : K[X]) * a1 * a4 * a7 * H ^ 36 +
    (1546188226560 : K[X]) * a1 * a5 * a6 * H ^ 36 +
    (1288490188800 : K[X]) * a2 * a3 * a7 * H ^ 36 +
    (1546188226560 : K[X]) * a2 * a4 * a6 * H ^ 36 +
    (1803886264320 : K[X]) * a2 * a5 ^ 2 * H ^ 36 +
    (773094113280 : K[X]) * a3 ^ 2 * a6 * H ^ 36 +
    (3607772528640 : K[X]) * a3 * a4 * a5 * H ^ 36 +
    (601295421440 : K[X]) * a4 ^ 3 * H ^ 36 -
    (1443109011456 : K[X]) * a0 * b7 * a7 * H ^ 35 -
    (1443109011456 : K[X]) * a1 * b7 * a6 * H ^ 35 -
    (1236950581248 : K[X]) * a1 * b6 * a7 * H ^ 35 -
    (1443109011456 : K[X]) * a2 * a5 * b7 * H ^ 35 -
    (1236950581248 : K[X]) * a2 * b6 * a6 * H ^ 35 -
    (1030792151040 : K[X]) * a2 * b5 * a7 * H ^ 35 -
    (1443109011456 : K[X]) * a3 * a4 * b7 * H ^ 35 -
    (1236950581248 : K[X]) * a3 * a5 * b6 * H ^ 35 -
    (1030792151040 : K[X]) * a3 * b5 * a6 * H ^ 35 -
    (824633720832 : K[X]) * a3 * b4 * a7 * H ^ 35 -
    (618475290624 : K[X]) * a4 ^ 2 * b6 * H ^ 35 -
    (1030792151040 : K[X]) * a4 * a5 * b5 * H ^ 35 -
    (824633720832 : K[X]) * a4 * b4 * a6 * H ^ 35 -
    (618475290624 : K[X]) * a4 * b3 * a7 * H ^ 35 -
    (412316860416 : K[X]) * a5 ^ 2 * b4 * H ^ 35 -
    (618475290624 : K[X]) * a5 * b3 * a6 * H ^ 35 -
    (412316860416 : K[X]) * a5 * b2 * a7 * H ^ 35 -
    (206158430208 : K[X]) * b2 * a6 ^ 2 * H ^ 35 -
    (206158430208 : K[X]) * b1 * a6 * a7 * H ^ 35 +
    (644245094400 : K[X]) * a0 * a6 * a7 ^ 2 * H ^ 32 -
    (1159641169920 : K[X]) * a1 * a5 * a7 ^ 2 * H ^ 32 +
    (676457349120 : K[X]) * a1 * a6 ^ 2 * a7 * H ^ 32 -
    (1159641169920 : K[X]) * a2 * a4 * a7 ^ 2 * H ^ 32 -
    (2254857830400 : K[X]) * a2 * a5 * a6 * a7 * H ^ 32 +
    (150323855360 : K[X]) * a2 * a6 ^ 3 * H ^ 32 -
    (579820584960 : K[X]) * a3 ^ 2 * a7 ^ 2 * H ^ 32 -
    (2254857830400 : K[X]) * a3 * a4 * a6 * a7 * H ^ 32 -
    (2931315179520 : K[X]) * a3 * a5 ^ 2 * a7 * H ^ 32 -
    (1352914698240 : K[X]) * a3 * a5 * a6 ^ 2 * H ^ 32 -
    (2931315179520 : K[X]) * a4 ^ 2 * a5 * a7 * H ^ 32 -
    (676457349120 : K[X]) * a4 ^ 2 * a6 ^ 2 * H ^ 32 -
    (3156800962560 : K[X]) * a4 * a5 ^ 2 * a6 * H ^ 32 -
    (413390602240 : K[X]) * a5 ^ 4 * H ^ 32 +
    (1262720385024 : K[X]) * a1 * b7 * a7 ^ 2 * H ^ 31 +
    (2525440770048 : K[X]) * a2 * b7 * a6 * a7 * H ^ 31 +
    (1082331758592 : K[X]) * a2 * b6 * a7 ^ 2 * H ^ 31 +
    (2525440770048 : K[X]) * a3 * a5 * b7 * a7 * H ^ 31 +
    (1262720385024 : K[X]) * a3 * b7 * a6 ^ 2 * H ^ 31 +
    (2164663517184 : K[X]) * a3 * b6 * a6 * a7 * H ^ 31 +
    (901943132160 : K[X]) * a3 * b5 * a7 ^ 2 * H ^ 31 +
    (1262720385024 : K[X]) * a4 ^ 2 * b7 * a7 * H ^ 31 +
    (2525440770048 : K[X]) * a4 * a5 * b7 * a6 * H ^ 31 +
    (2164663517184 : K[X]) * a4 * a5 * b6 * a7 * H ^ 31 +
    (1082331758592 : K[X]) * a4 * b6 * a6 ^ 2 * H ^ 31 +
    (1803886264320 : K[X]) * a4 * b5 * a6 * a7 * H ^ 31 +
    (721554505728 : K[X]) * a4 * b4 * a7 ^ 2 * H ^ 31 +
    (420906795008 : K[X]) * a5 ^ 3 * b7 * H ^ 31 +
    (1082331758592 : K[X]) * a5 ^ 2 * b6 * a6 * H ^ 31 +
    (901943132160 : K[X]) * a5 ^ 2 * b5 * a7 * H ^ 31 +
    (901943132160 : K[X]) * a5 * b5 * a6 ^ 2 * H ^ 31 +
    (1443109011456 : K[X]) * a5 * b4 * a6 * a7 * H ^ 31 +
    (541165879296 : K[X]) * a5 * b3 * a7 ^ 2 * H ^ 31 +
    (240518168576 : K[X]) * b4 * a6 ^ 3 * H ^ 31 +
    (541165879296 : K[X]) * b3 * a6 ^ 2 * a7 * H ^ 31 +
    (360777252864 : K[X]) * b2 * a6 * a7 ^ 2 * H ^ 31 +
    (60129542144 : K[X]) * b1 * a7 ^ 3 * H ^ 31 -
    (84557168640 : K[X]) * a0 * a7 ^ 4 * H ^ 28 -
    (582504939520 : K[X]) * a1 * a6 * a7 ^ 3 * H ^ 28 +
    (1071057469440 : K[X]) * a2 * a5 * a7 ^ 3 * H ^ 28 -
    (1014686023680 : K[X]) * a2 * a6 ^ 2 * a7 ^ 2 * H ^ 28 +
    (1071057469440 : K[X]) * a3 * a4 * a7 ^ 3 * H ^ 28 +
    (2931315179520 : K[X]) * a3 * a5 * a6 * a7 ^ 2 * H ^ 28 -
    (620085903360 : K[X]) * a3 * a6 ^ 3 * a7 * H ^ 28 +
    (1465657589760 : K[X]) * a4 ^ 2 * a6 * a7 ^ 2 * H ^ 28 +
    (3946001203200 : K[X]) * a4 * a5 ^ 2 * a7 ^ 2 * H ^ 28 +
    (3100429516800 : K[X]) * a4 * a5 * a6 ^ 2 * a7 * H ^ 28 -
    (103347650560 : K[X]) * a4 * a6 ^ 4 * H ^ 28 +
    (2687038914560 : K[X]) * a5 ^ 3 * a6 * a7 * H ^ 28 +
    (620085903360 : K[X]) * a5 ^ 2 * a6 ^ 3 * H ^ 28 -
    (1157493686272 : K[X]) * a2 * b7 * a7 ^ 3 * H ^ 27 -
    (3472481058816 : K[X]) * a3 * b7 * a6 * a7 ^ 2 * H ^ 27 -
    (992137445376 : K[X]) * a3 * b6 * a7 ^ 3 * H ^ 27 -
    (3472481058816 : K[X]) * a4 * a5 * b7 * a7 ^ 2 * H ^ 27 -
    (3472481058816 : K[X]) * a4 * b7 * a6 ^ 2 * a7 * H ^ 27 -
    (2976412336128 : K[X]) * a4 * b6 * a6 * a7 ^ 2 * H ^ 27 -
    (826781204480 : K[X]) * a4 * b5 * a7 ^ 3 * H ^ 27 -
    (3472481058816 : K[X]) * a5 ^ 2 * b7 * a6 * a7 * H ^ 27 -
    (1488206168064 : K[X]) * a5 ^ 2 * b6 * a7 ^ 2 * H ^ 27 -
    (1157493686272 : K[X]) * a5 * b7 * a6 ^ 3 * H ^ 27 -
    (2976412336128 : K[X]) * a5 * b6 * a6 ^ 2 * a7 * H ^ 27 -
    (2480343613440 : K[X]) * a5 * b5 * a6 * a7 ^ 2 * H ^ 27 -
    (661424963584 : K[X]) * a5 * b4 * a7 ^ 3 * H ^ 27 -
    (248034361344 : K[X]) * b6 * a6 ^ 4 * H ^ 27 -
    (826781204480 : K[X]) * b5 * a6 ^ 3 * a7 * H ^ 27 -
    (992137445376 : K[X]) * b4 * a6 ^ 2 * a7 ^ 2 * H ^ 27 -
    (496068722688 : K[X]) * b3 * a6 * a7 ^ 3 * H ^ 27 -
    (82678120448 : K[X]) * b2 * a7 ^ 4 * H ^ 27 +
    (64592281600 : K[X]) * a1 * a7 ^ 5 * H ^ 24 +
    (542575165440 : K[X]) * a2 * a6 * a7 ^ 4 * H ^ 24 -
    (1007639592960 : K[X]) * a3 * a5 * a7 ^ 4 * H ^ 24 +
    (1317682544640 : K[X]) * a3 * a6 ^ 2 * a7 ^ 3 * H ^ 24 -
    (503819796480 : K[X]) * a4 ^ 2 * a7 ^ 4 * H ^ 24 -
    (3565493944320 : K[X]) * a4 * a5 * a6 * a7 ^ 3 * H ^ 24 +
    (1343519457280 : K[X]) * a4 * a6 ^ 3 * a7 ^ 2 * H ^ 24 -
    (1627725496320 : K[X]) * a5 ^ 3 * a7 ^ 3 * H ^ 24 -
    (2635365089280 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 ^ 2 * H ^ 24 +
    (581330534400 : K[X]) * a5 * a6 ^ 4 * a7 * H ^ 24 +
    (64592281600 : K[X]) * a6 ^ 6 * H ^ 24 +
    (1085150330880 : K[X]) * a3 * b7 * a7 ^ 4 * H ^ 23 +
    (4340601323520 : K[X]) * a4 * b7 * a6 * a7 ^ 3 * H ^ 23 +
    (930128855040 : K[X]) * a4 * b6 * a7 ^ 4 * H ^ 23 +
    (2170300661760 : K[X]) * a5 ^ 2 * b7 * a7 ^ 3 * H ^ 23 +
    (6510901985280 : K[X]) * a5 * b7 * a6 ^ 2 * a7 ^ 2 * H ^ 23 +
    (3720515420160 : K[X]) * a5 * b6 * a6 * a7 ^ 3 * H ^ 23 +
    (775107379200 : K[X]) * a5 * b5 * a7 ^ 4 * H ^ 23 +
    (1085150330880 : K[X]) * b7 * a6 ^ 4 * a7 * H ^ 23 +
    (1860257710080 : K[X]) * b6 * a6 ^ 3 * a7 ^ 2 * H ^ 23 +
    (1550214758400 : K[X]) * b5 * a6 ^ 2 * a7 ^ 3 * H ^ 23 +
    (620085903360 : K[X]) * b4 * a6 * a7 ^ 4 * H ^ 23 +
    (93012885504 : K[X]) * b3 * a7 ^ 5 * H ^ 23 -
    (51673825280 : K[X]) * a2 * a7 ^ 6 * H ^ 20 -
    (513508638720 : K[X]) * a3 * a6 * a7 ^ 5 * H ^ 20 +
    (959195381760 : K[X]) * a4 * a5 * a7 ^ 5 * H ^ 20 -
    (1598658969600 : K[X]) * a4 * a6 ^ 2 * a7 ^ 4 * H ^ 20 +
    (2083101081600 : K[X]) * a5 ^ 2 * a6 * a7 ^ 4 * H ^ 20 -
    (2293025996800 : K[X]) * a5 * a6 ^ 3 * a7 ^ 3 * H ^ 20 -
    (1065772646400 : K[X]) * a6 ^ 5 * a7 ^ 2 * H ^ 20 -
    (1030892814336 : K[X]) * a4 * b7 * a7 ^ 5 * H ^ 19 -
    (5154464071680 : K[X]) * a5 * b7 * a6 * a7 ^ 4 * H ^ 19 -
    (883622412288 : K[X]) * a5 * b6 * a7 ^ 5 * H ^ 19 -
    (3436309381120 : K[X]) * b7 * a6 ^ 3 * a7 ^ 3 * H ^ 19 -
    (2209056030720 : K[X]) * b6 * a6 ^ 2 * a7 ^ 4 * H ^ 19 -
    (736352010240 : K[X]) * b5 * a6 * a7 ^ 5 * H ^ 19 -
    (98180268032 : K[X]) * b4 * a7 ^ 6 * H ^ 19 +
    (42734714880 : K[X]) * a3 * a7 ^ 7 * H ^ 16 +
    (490901340160 : K[X]) * a4 * a6 * a7 ^ 6 * H ^ 16 -
    (460220006400 : K[X]) * a5 ^ 2 * a7 ^ 6 * H ^ 16 +
    (1863891025920 : K[X]) * a5 * a6 ^ 2 * a7 ^ 5 * H ^ 16 +
    (2627089203200 : K[X]) * a6 ^ 4 * a7 ^ 4 * H ^ 16 +
    (987938947072 : K[X]) * a5 * b7 * a7 ^ 6 * H ^ 15 +
    (2963816841216 : K[X]) * b7 * a6 ^ 2 * a7 ^ 5 * H ^ 15 +
    (846804811776 : K[X]) * b6 * a6 * a7 ^ 6 * H ^ 15 +
    (100810096640 : K[X]) * b5 * a7 ^ 7 * H ^ 15 -
    (36228628480 : K[X]) * a4 * a7 ^ 8 * H ^ 12 -
    (472547328000 : K[X]) * a5 * a6 * a7 ^ 7 * H ^ 12 -
    (2293429698560 : K[X]) * a6 ^ 3 * a7 ^ 6 * H ^ 12 -
    (952655413248 : K[X]) * b7 * a6 * a7 ^ 7 * H ^ 11 -
    (102070222848 : K[X]) * b6 * a7 ^ 8 * H ^ 11 +
    (31306260480 : K[X]) * a5 * a7 ^ 9 * H ^ 8 +
    (887798292480 : K[X]) * a6 ^ 2 * a7 ^ 8 * H ^ 8 +
    (102542770176 : K[X]) * b7 * a7 ^ 9 * H ^ 7 -
    (155645276160 : K[X]) * a6 * a7 ^ 10 * H ^ 4 +
    (10013942400 : K[X]) * a7 ^ 12 +
    Polynomial.C κ *
      (-(51539607552 : K[X]) * a0 * a6 * H ^ 39 -
        (51539607552 : K[X]) * a1 * a5 * H ^ 39 -
        (51539607552 : K[X]) * a2 * a4 * H ^ 39 -
        (25769803776 : K[X]) * a3 ^ 2 * H ^ 39 +
        (45097156608 : K[X]) * a0 * a7 ^ 2 * H ^ 35 +
        (90194313216 : K[X]) * a1 * a6 * a7 * H ^ 35 +
        (90194313216 : K[X]) * a2 * a5 * a7 * H ^ 35 +
        (45097156608 : K[X]) * a2 * a6 ^ 2 * H ^ 35 +
        (90194313216 : K[X]) * a3 * a4 * a7 * H ^ 35 +
        (90194313216 : K[X]) * a3 * a5 * a6 * H ^ 35 +
        (45097156608 : K[X]) * a4 ^ 2 * a6 * H ^ 35 +
        (45097156608 : K[X]) * a4 * a5 ^ 2 * H ^ 35 -
        (41339060224 : K[X]) * a1 * a7 ^ 3 * H ^ 31 -
        (124017180672 : K[X]) * a2 * a6 * a7 ^ 2 * H ^ 31 -
        (124017180672 : K[X]) * a3 * a5 * a7 ^ 2 * H ^ 31 -
        (124017180672 : K[X]) * a3 * a6 ^ 2 * a7 * H ^ 31 -
        (62008590336 : K[X]) * a4 ^ 2 * a7 ^ 2 * H ^ 31 -
        (248034361344 : K[X]) * a4 * a5 * a6 * a7 * H ^ 31 -
        (41339060224 : K[X]) * a4 * a6 ^ 3 * H ^ 31 -
        (41339060224 : K[X]) * a5 ^ 3 * a7 * H ^ 31 -
        (62008590336 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 31 +
        (38755368960 : K[X]) * a2 * a7 ^ 4 * H ^ 27 +
        (155021475840 : K[X]) * a3 * a6 * a7 ^ 3 * H ^ 27 +
        (155021475840 : K[X]) * a4 * a5 * a7 ^ 3 * H ^ 27 +
        (232532213760 : K[X]) * a4 * a6 ^ 2 * a7 ^ 2 * H ^ 27 +
        (232532213760 : K[X]) * a5 ^ 2 * a6 * a7 ^ 2 * H ^ 27 +
        (155021475840 : K[X]) * a5 * a6 ^ 3 * a7 * H ^ 27 +
        (7751073792 : K[X]) * a6 ^ 5 * H ^ 27 -
        (36817600512 : K[X]) * a3 * a7 ^ 5 * H ^ 23 -
        (184088002560 : K[X]) * a4 * a6 * a7 ^ 4 * H ^ 23 -
        (92044001280 : K[X]) * a5 ^ 2 * a7 ^ 4 * H ^ 23 -
        (368176005120 : K[X]) * a5 * a6 ^ 2 * a7 ^ 3 * H ^ 23 -
        (92044001280 : K[X]) * a6 ^ 4 * a7 ^ 2 * H ^ 23 +
        (35283533824 : K[X]) * a4 * a7 ^ 6 * H ^ 19 +
        (211701202944 : K[X]) * a5 * a6 * a7 ^ 5 * H ^ 19 +
        (176417669120 : K[X]) * a6 ^ 3 * a7 ^ 4 * H ^ 19 -
        (34023407616 : K[X]) * a5 * a7 ^ 7 * H ^ 15 -
        (119081926656 : K[X]) * a6 ^ 2 * a7 ^ 6 * H ^ 15 +
        (32960176128 : K[X]) * a6 * a7 ^ 8 * H ^ 11 -
        (3204461568 : K[X]) * a7 ^ 10 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`5` Jacobian expression with the
weighted derivative of `N₁₂`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` through
degree-`6` rows.  The row sees only `q₀, …, q₆`, so no `N`- and no
`C`-correction occurs at all; for the first time two integral-tower
rows (`N₁₀` and `N₁₁`) correct simultaneously, and `q₀` couples only
through the `N₁₀`-row correction. -/
theorem alignedTwelfthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    (274877906944 : K[X]) * H ^ 40 *
        (a5.derivative * b1 +
          a4.derivative * (b2 * (2 : K[X])) +
          a3.derivative * (b3 * (3 : K[X])) +
          a2.derivative * (b4 * (4 : K[X])) +
          a1.derivative * (b5 * (5 : K[X])) +
          a0.derivative * (b6 * (6 : K[X])) -
        ((a6 * (6 : K[X])) * b0.derivative +
          (a5 * (5 : K[X])) * b1.derivative +
          (a4 * (4 : K[X])) * b2.derivative +
          (a3 * (3 : K[X])) * b3.derivative +
          (a2 * (2 : K[X])) * b4.derivative +
          a1 * b5.derivative)) =
      (H *
          (alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ).derivative -
        (42 : K[X]) *
          alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ * H.derivative) +
        ((5637144576 : K[X]) * a0 * a7 * H ^ 28 +
            (5637144576 : K[X]) * a1 * a6 * H ^ 28 +
            (5637144576 : K[X]) * a2 * a5 * H ^ 28 +
            (5637144576 : K[X]) * a3 * a4 * H ^ 28 -
            (352321536 : K[X]) * a1 * a7 ^ 2 * H ^ 24 -
            (704643072 : K[X]) * a2 * a6 * a7 * H ^ 24 -
            (704643072 : K[X]) * a3 * a5 * a7 * H ^ 24 -
            (352321536 : K[X]) * a3 * a6 ^ 2 * H ^ 24 -
            (352321536 : K[X]) * a4 ^ 2 * a7 * H ^ 24 -
            (704643072 : K[X]) * a4 * a5 * a6 * H ^ 24 -
            (117440512 : K[X]) * a5 ^ 3 * H ^ 24 +
            (132120576 : K[X]) * a2 * a7 ^ 3 * H ^ 20 +
            (396361728 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 20 +
            (396361728 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 20 +
            (396361728 : K[X]) * a4 * a6 ^ 2 * a7 * H ^ 20 +
            (396361728 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 20 +
            (132120576 : K[X]) * a5 * a6 ^ 3 * H ^ 20 -
            (70189056 : K[X]) * a3 * a7 ^ 4 * H ^ 16 -
            (280756224 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 16 -
            (140378112 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 16 -
            (421134336 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 16 -
            (70189056 : K[X]) * a6 ^ 4 * a7 * H ^ 16 +
            (43868160 : K[X]) * a4 * a7 ^ 5 * H ^ 12 +
            (219340800 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 12 +
            (146227200 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 12 -
            (30159360 : K[X]) * a5 * a7 ^ 6 * H ^ 8 -
            (90478080 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 8 +
            (22080960 : K[X]) * a6 * a7 ^ 7 * H ^ 4 -
            (1878415 : K[X]) * a7 ^ 9) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((805306368 : K[X]) * a0 * H ^ 28 +
            (603979776 : K[X]) * a1 * a7 * H ^ 24 +
            (603979776 : K[X]) * a2 * a6 * H ^ 24 +
            (603979776 : K[X]) * a3 * a5 * H ^ 24 +
            (301989888 : K[X]) * a4 ^ 2 * H ^ 24 -
            (75497472 : K[X]) * a2 * a7 ^ 2 * H ^ 20 -
            (150994944 : K[X]) * a3 * a6 * a7 * H ^ 20 -
            (150994944 : K[X]) * a4 * a5 * a7 * H ^ 20 -
            (75497472 : K[X]) * a4 * a6 ^ 2 * H ^ 20 -
            (75497472 : K[X]) * a5 ^ 2 * a6 * H ^ 20 +
            (31457280 : K[X]) * a3 * a7 ^ 3 * H ^ 16 +
            (94371840 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 16 +
            (47185920 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 16 +
            (94371840 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 16 +
            (7864320 : K[X]) * a6 ^ 4 * H ^ 16 -
            (17694720 : K[X]) * a4 * a7 ^ 4 * H ^ 12 -
            (70778880 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 12 -
            (35389440 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 12 +
            (11501568 : K[X]) * a5 * a7 ^ 5 * H ^ 8 +
            (28753920 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 8 -
            (8146944 : K[X]) * a6 * a7 ^ 6 * H ^ 4 +
            (763776 : K[X]) * a7 ^ 8) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((50331648 : K[X]) * a1 * H ^ 24 +
            (31457280 : K[X]) * a2 * a7 * H ^ 20 +
            (31457280 : K[X]) * a3 * a6 * H ^ 20 +
            (31457280 : K[X]) * a4 * a5 * H ^ 20 -
            (5898240 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
            (11796480 : K[X]) * a4 * a6 * a7 * H ^ 16 -
            (5898240 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
            (5898240 : K[X]) * a5 * a6 ^ 2 * H ^ 16 +
            (2703360 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
            (8110080 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
            (2703360 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
            (1605120 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
            (3210240 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
            (1083456 : K[X]) * a6 * a7 ^ 5 * H ^ 4 -
            (112860 : K[X]) * a7 ^ 7) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((25165824 : K[X]) * a2 * H ^ 20 +
            (12582912 : K[X]) * a3 * a7 * H ^ 16 +
            (12582912 : K[X]) * a4 * a6 * H ^ 16 +
            (6291456 : K[X]) * a5 ^ 2 * H ^ 16 -
            (3145728 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (6291456 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (1048576 : K[X]) * a6 ^ 3 * H ^ 12 +
            (1572864 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (2359296 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (983040 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (114688 : K[X]) * a7 ^ 6) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((196608 : K[X]) * a3 * H ^ 16 +
            (73728 : K[X]) * a4 * a7 * H ^ 12 +
            (73728 : K[X]) * a5 * a6 * H ^ 12 -
            (23040 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (23040 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (12480 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (1638 : K[X]) * a7 ^ 5) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        ((49152 : K[X]) * a4 * H ^ 12 +
            (12288 : K[X]) * a5 * a7 * H ^ 8 +
            (6144 : K[X]) * a6 ^ 2 * H ^ 8 -
            (4608 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (672 : K[X]) * a7 ^ 4) *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        ((1536 : K[X]) * a5 * H ^ 8 +
            (192 : K[X]) * a6 * a7 * H ^ 4 -
            (28 : K[X]) * a7 ^ 3) *
          ((2 : K[X]) * H *
              (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ).derivative -
            (63 : K[X]) *
              alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        (1536 : K[X]) * a6 * H ^ 4 *
          (H * (alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (35 : K[X]) *
              alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        (3 : K[X]) * a7 *
          ((2 : K[X]) * H *
              (alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (77 : K[X]) *
              alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedTwelfthDefect810, alignedEleventhDefect810,
    alignedTenthDefect810, alignedNinthDefect810, alignedEighthDefect810,
    alignedSeventhDefect810, alignedSixthDefect810, alignedFifthDefect810,
    alignedFourthDefect810, alignedThirdDefect810,
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
degree-`6` rows, the degree-`5` row is the weighted derivative
`H N₁₂' - 42 N₁₂ H' = 0`. -/
theorem alignedTwelfthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H *
        (alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (42 : K[X]) *
        alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedTwelfthCoefficientJacobianRow_810 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6] at hrow
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
  have hid := alignedTwelfthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 0) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) κ
  rw [hrow, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ, hrowL, hrowN,
    hrowN11] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-eighty-four polynomial first integral of the aligned
`(8,10)` twelfth defect: `N₁₂ = κ₁₁ H⁴²`.  The weight is even, so the
integral is chamber-free and `κ₁₁` is preserved in both chambers. -/
theorem alignedTwelfthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₁₁ : K,
      alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₁₁ * H ^ 42 := by
  let N : K[X] :=
    alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow :
      H * N.derivative - (42 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      alignedTwelfthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC42 : Polynomial.C (42 : K) = (42 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian N (H ^ 42) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      N * (Polynomial.C (42 : K) * H ^ (42 - 1) * H.derivative) -
          N.derivative * H ^ 42 =
          H ^ 41 *
            (Polynomial.C (42 : K) * N * H.derivative -
              H * N.derivative) := by
        ring
      _ = 0 := by
        rw [hC42]
        have hfac :
            (42 : K[X]) * N * H.derivative - H * N.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 42 hH) hW

/-! ## Root dodecic of the factored transport and its absorption -/

/-- Evaluating a factored-transport twelfth row at a root of its
co-factor: the root dodecic `853461 g¹² - 12270960 p₆ g¹⁰
+ 67374912 p₆² g⁸ - 175142912 p₆³ g⁶ + 214609920 p₆⁴ g⁴
- 103219200 p₆⁵ g² + 9175040 p₆⁶` vanishes there.  The dodecic is even
in `g` with a pure `p₆⁶` tail, so no `g`-factor splits off; it is not
excluded as an identity. -/
theorem alignedTwelfth_factored_rootDodecic_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (7040 : K[X]) *
        ((853461 : K[X]) * g ^ 12 - (12270960 : K[X]) * a6 * g ^ 10 +
          (67374912 : K[X]) * a6 ^ 2 * g ^ 8 -
          (175142912 : K[X]) * a6 ^ 3 * g ^ 6 +
          (214609920 : K[X]) * a6 ^ 4 * g ^ 4 -
          (103219200 : K[X]) * a6 ^ 5 * g ^ 2 +
          (9175040 : K[X]) * a6 ^ 6) =
      W)
    {a : K} (hW : W.eval a = 0) :
    853461 * (g.eval a) ^ 12 - 12270960 * a6.eval a * (g.eval a) ^ 10 +
      67374912 * (a6.eval a) ^ 2 * (g.eval a) ^ 8 -
      175142912 * (a6.eval a) ^ 3 * (g.eval a) ^ 6 +
      214609920 * (a6.eval a) ^ 4 * (g.eval a) ^ 4 -
      103219200 * (a6.eval a) ^ 5 * (g.eval a) ^ 2 +
      9175040 * (a6.eval a) ^ 6 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  have hs := (mul_eq_zero.mp hev).resolve_left
    (by norm_num : (7040 : K) ≠ 0)
  linear_combination hs

/-- The root dodecic of the consumed degree-`5` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the twelfth row adds no new root
constraint. -/
theorem alignedTwelfth_rootDodecic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    853461 * G ^ 12 - 12270960 * P6 * G ^ 10 + 67374912 * P6 ^ 2 * G ^ 8 -
      175142912 * P6 ^ 3 * G ^ 6 + 214609920 * P6 ^ 4 * G ^ 4 -
      103219200 * P6 ^ 5 * G ^ 2 + 9175040 * P6 ^ 6 = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared twelfth rows and transport co-factors -/

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the square-chamber twelfth row (`H = h₀²`,
`p₇ = h₀⁴ g₁`, `h₀⁴⁸` peeled, `128 q₇ h₀²` consumed): `q₁, …, q₆` sit
at `h₀³²` here, i.e. at `h₀³⁶` in the cleared row. -/
def alignedTwelfthSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
    -(2061584302080 : K[X]) * a0 * a4 * h0 ^ 28 -
    (2061584302080 : K[X]) * a1 * a3 * h0 ^ 28 -
    (1030792151040 : K[X]) * a2 ^ 2 * h0 ^ 28 +
    (1649267441664 : K[X]) * a0 * b6 * h0 ^ 26 +
    (1374389534720 : K[X]) * a1 * b5 * h0 ^ 26 +
    (1099511627776 : K[X]) * a2 * b4 * h0 ^ 26 +
    (824633720832 : K[X]) * a3 * b3 * h0 ^ 26 +
    (549755813888 : K[X]) * a4 * b2 * h0 ^ 26 +
    (274877906944 : K[X]) * a5 * b1 * h0 ^ 26 -
    (515396075520 : K[X]) * a0 * a5 * g1 * h0 ^ 24 +
    (1288490188800 : K[X]) * a1 * a4 * g1 * h0 ^ 24 +
    (1288490188800 : K[X]) * a2 * a3 * g1 * h0 ^ 24 -
    (1236950581248 : K[X]) * a1 * b6 * g1 * h0 ^ 22 -
    (1030792151040 : K[X]) * a2 * b5 * g1 * h0 ^ 22 -
    (824633720832 : K[X]) * a3 * b4 * g1 * h0 ^ 22 -
    (618475290624 : K[X]) * a4 * b3 * g1 * h0 ^ 22 -
    (412316860416 : K[X]) * a5 * b2 * g1 * h0 ^ 22 -
    (206158430208 : K[X]) * b1 * a6 * g1 * h0 ^ 22 +
    (60129542144 : K[X]) * b1 * g1 ^ 3 * h0 ^ 22 -
    (257698037760 : K[X]) * a0 * a6 ^ 2 * h0 ^ 20 +
    (193273528320 : K[X]) * a0 * a6 * g1 ^ 2 * h0 ^ 20 -
    (28185722880 : K[X]) * a0 * g1 ^ 4 * h0 ^ 20 -
    (257698037760 : K[X]) * a1 * a5 * a6 * h0 ^ 20 +
    (418759311360 : K[X]) * a1 * a5 * g1 ^ 2 * h0 ^ 20 +
    (1546188226560 : K[X]) * a2 * a4 * a6 * h0 ^ 20 -
    (1159641169920 : K[X]) * a2 * a4 * g1 ^ 2 * h0 ^ 20 +
    (773094113280 : K[X]) * a3 ^ 2 * a6 * h0 ^ 20 -
    (579820584960 : K[X]) * a3 ^ 2 * g1 ^ 2 * h0 ^ 20 +
    (1803886264320 : K[X]) * a3 * a4 * a5 * h0 ^ 20 +
    (601295421440 : K[X]) * a4 ^ 3 * h0 ^ 20 -
    (1236950581248 : K[X]) * a2 * b6 * a6 * h0 ^ 18 +
    (1082331758592 : K[X]) * a2 * b6 * g1 ^ 2 * h0 ^ 18 -
    (1236950581248 : K[X]) * a3 * a5 * b6 * h0 ^ 18 -
    (1030792151040 : K[X]) * a3 * b5 * a6 * h0 ^ 18 +
    (901943132160 : K[X]) * a3 * b5 * g1 ^ 2 * h0 ^ 18 -
    (618475290624 : K[X]) * a4 ^ 2 * b6 * h0 ^ 18 -
    (1030792151040 : K[X]) * a4 * a5 * b5 * h0 ^ 18 -
    (824633720832 : K[X]) * a4 * b4 * a6 * h0 ^ 18 +
    (721554505728 : K[X]) * a4 * b4 * g1 ^ 2 * h0 ^ 18 -
    (412316860416 : K[X]) * a5 ^ 2 * b4 * h0 ^ 18 -
    (618475290624 : K[X]) * a5 * b3 * a6 * h0 ^ 18 +
    (541165879296 : K[X]) * a5 * b3 * g1 ^ 2 * h0 ^ 18 -
    (206158430208 : K[X]) * b2 * a6 ^ 2 * h0 ^ 18 +
    (360777252864 : K[X]) * b2 * a6 * g1 ^ 2 * h0 ^ 18 -
    (82678120448 : K[X]) * b2 * g1 ^ 4 * h0 ^ 18 +
    (225485783040 : K[X]) * a1 * a6 ^ 2 * g1 * h0 ^ 16 -
    (131533373440 : K[X]) * a1 * a6 * g1 ^ 3 * h0 ^ 16 +
    (15267266560 : K[X]) * a1 * g1 ^ 5 * h0 ^ 16 +
    (450971566080 : K[X]) * a2 * a5 * a6 * g1 * h0 ^ 16 -
    (319438192640 : K[X]) * a2 * a5 * g1 ^ 3 * h0 ^ 16 -
    (2705829396480 : K[X]) * a3 * a4 * a6 * g1 * h0 ^ 16 +
    (1127428915200 : K[X]) * a3 * a4 * g1 ^ 3 * h0 ^ 16 +
    (225485783040 : K[X]) * a3 * a5 ^ 2 * g1 * h0 ^ 16 -
    (1352914698240 : K[X]) * a4 ^ 2 * a5 * g1 * h0 ^ 16 +
    (2164663517184 : K[X]) * a3 * b6 * a6 * g1 * h0 ^ 14 -
    (992137445376 : K[X]) * a3 * b6 * g1 ^ 3 * h0 ^ 14 +
    (2164663517184 : K[X]) * a4 * a5 * b6 * g1 * h0 ^ 14 +
    (1803886264320 : K[X]) * a4 * b5 * a6 * g1 * h0 ^ 14 -
    (826781204480 : K[X]) * a4 * b5 * g1 ^ 3 * h0 ^ 14 +
    (901943132160 : K[X]) * a5 ^ 2 * b5 * g1 * h0 ^ 14 +
    (1443109011456 : K[X]) * a5 * b4 * a6 * g1 * h0 ^ 14 -
    (661424963584 : K[X]) * a5 * b4 * g1 ^ 3 * h0 ^ 14 +
    (541165879296 : K[X]) * b3 * a6 ^ 2 * g1 * h0 ^ 14 -
    (496068722688 : K[X]) * b3 * a6 * g1 ^ 3 * h0 ^ 14 +
    (93012885504 : K[X]) * b3 * g1 ^ 5 * h0 ^ 14 +
    (150323855360 : K[X]) * a2 * a6 ^ 3 * h0 ^ 12 -
    (225485783040 : K[X]) * a2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 12 +
    (82208358400 : K[X]) * a2 * a6 * g1 ^ 4 * h0 ^ 12 -
    (6459228160 : K[X]) * a2 * g1 ^ 6 * h0 ^ 12 +
    (225485783040 : K[X]) * a3 * a5 * a6 ^ 2 * h0 ^ 12 -
    (620085903360 : K[X]) * a3 * a5 * a6 * g1 ^ 2 * h0 ^ 12 +
    (250148290560 : K[X]) * a3 * a5 * g1 ^ 4 * h0 ^ 12 -
    (676457349120 : K[X]) * a4 ^ 2 * a6 ^ 2 * h0 ^ 12 +
    (1860257710080 : K[X]) * a4 ^ 2 * a6 * g1 ^ 2 * h0 ^ 12 -
    (553144811520 : K[X]) * a4 ^ 2 * g1 ^ 4 * h0 ^ 12 -
    (394600120320 : K[X]) * a4 * a5 ^ 2 * g1 ^ 2 * h0 ^ 12 +
    (112742891520 : K[X]) * a5 ^ 4 * h0 ^ 12 +
    (1082331758592 : K[X]) * a4 * b6 * a6 ^ 2 * h0 ^ 10 -
    (2976412336128 : K[X]) * a4 * b6 * a6 * g1 ^ 2 * h0 ^ 10 +
    (930128855040 : K[X]) * a4 * b6 * g1 ^ 4 * h0 ^ 10 +
    (1082331758592 : K[X]) * a5 ^ 2 * b6 * a6 * h0 ^ 10 -
    (1488206168064 : K[X]) * a5 ^ 2 * b6 * g1 ^ 2 * h0 ^ 10 +
    (901943132160 : K[X]) * a5 * b5 * a6 ^ 2 * h0 ^ 10 -
    (2480343613440 : K[X]) * a5 * b5 * a6 * g1 ^ 2 * h0 ^ 10 +
    (775107379200 : K[X]) * a5 * b5 * g1 ^ 4 * h0 ^ 10 +
    (240518168576 : K[X]) * b4 * a6 ^ 3 * h0 ^ 10 -
    (992137445376 : K[X]) * b4 * a6 ^ 2 * g1 ^ 2 * h0 ^ 10 +
    (620085903360 : K[X]) * b4 * a6 * g1 ^ 4 * h0 ^ 10 -
    (98180268032 : K[X]) * b4 * g1 ^ 6 * h0 ^ 10 -
    (225485783040 : K[X]) * a3 * a6 ^ 3 * g1 * h0 ^ 8 +
    (183207198720 : K[X]) * a3 * a6 ^ 2 * g1 ^ 3 * h0 ^ 8 -
    (38755368960 : K[X]) * a3 * a6 * g1 ^ 5 * h0 ^ 8 +
    (346030080 : K[X]) * a3 * g1 ^ 7 * h0 ^ 8 -
    (450971566080 : K[X]) * a4 * a5 * a6 ^ 2 * g1 * h0 ^ 8 +
    (676457349120 : K[X]) * a4 * a5 * a6 * g1 ^ 3 * h0 ^ 8 -
    (193776844800 : K[X]) * a4 * a5 * g1 ^ 5 * h0 ^ 8 -
    (1522029035520 : K[X]) * a5 ^ 3 * a6 * g1 * h0 ^ 8 +
    (1068708659200 : K[X]) * a5 ^ 3 * g1 ^ 3 * h0 ^ 8 -
    (2976412336128 : K[X]) * a5 * b6 * a6 ^ 2 * g1 * h0 ^ 6 +
    (3720515420160 : K[X]) * a5 * b6 * a6 * g1 ^ 3 * h0 ^ 6 -
    (883622412288 : K[X]) * a5 * b6 * g1 ^ 5 * h0 ^ 6 -
    (826781204480 : K[X]) * b5 * a6 ^ 3 * g1 * h0 ^ 6 +
    (1550214758400 : K[X]) * b5 * a6 ^ 2 * g1 ^ 3 * h0 ^ 6 -
    (736352010240 : K[X]) * b5 * a6 * g1 ^ 5 * h0 ^ 6 +
    (100810096640 : K[X]) * b5 * g1 ^ 7 * h0 ^ 6 -
    (103347650560 : K[X]) * a4 * a6 ^ 4 * h0 ^ 4 +
    (258369126400 : K[X]) * a4 * a6 ^ 3 * g1 ^ 2 * h0 ^ 4 -
    (106577264640 : K[X]) * a4 * a6 ^ 2 * g1 ^ 4 * h0 ^ 4 -
    (807403520 : K[X]) * a4 * a6 * g1 ^ 6 * h0 ^ 4 +
    (4040622080 : K[X]) * a4 * g1 ^ 8 * h0 ^ 4 -
    (826781204480 : K[X]) * a5 ^ 2 * a6 ^ 3 * h0 ^ 4 +
    (4418112061440 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 ^ 2 * h0 ^ 4 -
    (3546116259840 : K[X]) * a5 ^ 2 * a6 * g1 ^ 4 * h0 ^ 4 +
    (689926307840 : K[X]) * a5 ^ 2 * g1 ^ 6 * h0 ^ 4 -
    (248034361344 : K[X]) * b6 * a6 ^ 4 * h0 ^ 2 +
    (1860257710080 : K[X]) * b6 * a6 ^ 3 * g1 ^ 2 * h0 ^ 2 -
    (2209056030720 : K[X]) * b6 * a6 ^ 2 * g1 ^ 4 * h0 ^ 2 +
    (846804811776 : K[X]) * b6 * a6 * g1 ^ 6 * h0 ^ 2 -
    (102070222848 : K[X]) * b6 * g1 ^ 8 * h0 ^ 2 +
    (1576051671040 : K[X]) * a5 * a6 ^ 4 * g1 -
    (4508541255680 : K[X]) * a5 * a6 ^ 3 * g1 ^ 3 +
    (3703559946240 : K[X]) * a5 * a6 ^ 2 * g1 ^ 5 -
    (1153289420800 : K[X]) * a5 * a6 * g1 ^ 7 +
    (120893358080 : K[X]) * a5 * g1 ^ 9 +
    Polynomial.C κ *
      (-(51539607552 : K[X]) * a0 * a6 * h0 ^ 26 -
        (51539607552 : K[X]) * a1 * a5 * h0 ^ 26 -
        (51539607552 : K[X]) * a2 * a4 * h0 ^ 26 -
        (25769803776 : K[X]) * a3 ^ 2 * h0 ^ 26 +
        (45097156608 : K[X]) * a1 * a6 * g1 * h0 ^ 22 -
        (1879048192 : K[X]) * a1 * g1 ^ 3 * h0 ^ 22 +
        (45097156608 : K[X]) * a2 * a5 * g1 * h0 ^ 22 +
        (45097156608 : K[X]) * a3 * a4 * g1 * h0 ^ 22 +
        (45097156608 : K[X]) * a2 * a6 ^ 2 * h0 ^ 18 -
        (45097156608 : K[X]) * a2 * a6 * g1 ^ 2 * h0 ^ 18 +
        (2583691264 : K[X]) * a2 * g1 ^ 4 * h0 ^ 18 +
        (90194313216 : K[X]) * a3 * a5 * a6 * h0 ^ 18 -
        (45097156608 : K[X]) * a3 * a5 * g1 ^ 2 * h0 ^ 18 +
        (45097156608 : K[X]) * a4 ^ 2 * a6 * h0 ^ 18 -
        (22548578304 : K[X]) * a4 ^ 2 * g1 ^ 2 * h0 ^ 18 +
        (45097156608 : K[X]) * a4 * a5 ^ 2 * h0 ^ 18 -
        (84557168640 : K[X]) * a3 * a6 ^ 2 * g1 * h0 ^ 14 +
        (46506442752 : K[X]) * a3 * a6 * g1 ^ 3 * h0 ^ 14 -
        (2906652672 : K[X]) * a3 * g1 ^ 5 * h0 ^ 14 -
        (169114337280 : K[X]) * a4 * a5 * a6 * g1 * h0 ^ 14 +
        (46506442752 : K[X]) * a4 * a5 * g1 ^ 3 * h0 ^ 14 -
        (28185722880 : K[X]) * a5 ^ 3 * g1 * h0 ^ 14 -
        (41339060224 : K[X]) * a4 * a6 ^ 3 * h0 ^ 10 +
        (124017180672 : K[X]) * a4 * a6 ^ 2 * g1 ^ 2 * h0 ^ 10 -
        (48444211200 : K[X]) * a4 * a6 * g1 ^ 4 * h0 ^ 10 +
        (3068133376 : K[X]) * a4 * g1 ^ 6 * h0 ^ 10 -
        (62008590336 : K[X]) * a5 ^ 2 * a6 ^ 2 * h0 ^ 10 +
        (124017180672 : K[X]) * a5 ^ 2 * a6 * g1 ^ 2 * h0 ^ 10 -
        (24222105600 : K[X]) * a5 ^ 2 * g1 ^ 4 * h0 ^ 10 +
        (118849798144 : K[X]) * a5 * a6 ^ 3 * g1 * h0 ^ 6 -
        (164710318080 : K[X]) * a5 * a6 ^ 2 * g1 ^ 3 * h0 ^ 6 +
        (50624200704 : K[X]) * a5 * a6 * g1 ^ 5 * h0 ^ 6 -
        (3150315520 : K[X]) * a5 * g1 ^ 7 * h0 ^ 6 +
        (7751073792 : K[X]) * a6 ^ 5 * h0 ^ 2 -
        (58133053440 : K[X]) * a6 ^ 4 * g1 ^ 2 * h0 ^ 2 +
        (69033000960 : K[X]) * a6 ^ 3 * g1 ^ 4 * h0 ^ 2 -
        (26462650368 : K[X]) * a6 ^ 2 * g1 ^ 6 * h0 ^ 2 +
        (3189694464 : K[X]) * a6 * g1 ^ 8 * h0 ^ 2) -
    Polynomial.C μ *
      (-(11274289152 : K[X]) * a0 * g1 * h0 ^ 29 -
        (11274289152 : K[X]) * a1 * a6 * h0 ^ 25 +
        (9865003008 : K[X]) * a1 * g1 ^ 2 * h0 ^ 25 -
        (11274289152 : K[X]) * a2 * a5 * h0 ^ 25 -
        (11274289152 : K[X]) * a3 * a4 * h0 ^ 25 +
        (19730006016 : K[X]) * a2 * a6 * g1 * h0 ^ 21 -
        (9042919424 : K[X]) * a2 * g1 ^ 3 * h0 ^ 21 +
        (19730006016 : K[X]) * a3 * a5 * g1 * h0 ^ 21 +
        (9865003008 : K[X]) * a4 ^ 2 * g1 * h0 ^ 21 +
        (9865003008 : K[X]) * a3 * a6 ^ 2 * h0 ^ 17 -
        (27128758272 : K[X]) * a3 * a6 * g1 ^ 2 * h0 ^ 17 +
        (8477736960 : K[X]) * a3 * g1 ^ 4 * h0 ^ 17 +
        (19730006016 : K[X]) * a4 * a5 * a6 * h0 ^ 17 -
        (27128758272 : K[X]) * a4 * a5 * g1 ^ 2 * h0 ^ 17 +
        (3288334336 : K[X]) * a5 ^ 3 * h0 ^ 17 -
        (27128758272 : K[X]) * a4 * a6 ^ 2 * g1 * h0 ^ 13 +
        (33910947840 : K[X]) * a4 * a6 * g1 ^ 3 * h0 ^ 13 -
        (8053850112 : K[X]) * a4 * g1 ^ 5 * h0 ^ 13 -
        (27128758272 : K[X]) * a5 ^ 2 * a6 * g1 * h0 ^ 13 +
        (16955473920 : K[X]) * a5 ^ 2 * g1 ^ 3 * h0 ^ 13 -
        (9042919424 : K[X]) * a5 * a6 ^ 3 * h0 ^ 9 +
        (50866421760 : K[X]) * a5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 9 -
        (40269250560 : K[X]) * a5 * a6 * g1 ^ 4 * h0 ^ 9 +
        (7718273024 : K[X]) * a5 * g1 ^ 6 * h0 ^ 9 +
        (8477736960 : K[X]) * a6 ^ 4 * g1 * h0 ^ 5 -
        (26846167040 : K[X]) * a6 ^ 3 * g1 ^ 3 * h0 ^ 5 +
        (23154819072 : K[X]) * a6 ^ 2 * g1 ^ 5 * h0 ^ 5 -
        (7442620416 : K[X]) * a6 * g1 ^ 7 * h0 ^ 5 +
        (801115392 : K[X]) * g1 ^ 9 * h0 ^ 5)

/-- Cleared twelfth row of the square chamber, in factored form: `h₀⁴`
times the transport co-factor plus the pure `g₁, p₆` dodecic block. -/
def alignedTwelfthSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedTwelfthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ μ +
    (7040 : K[X]) *
      ((853461 : K[X]) * g1 ^ 12 - (12270960 : K[X]) * a6 * g1 ^ 10 +
        (67374912 : K[X]) * a6 ^ 2 * g1 ^ 8 -
        (175142912 : K[X]) * a6 ^ 3 * g1 ^ 6 +
        (214609920 : K[X]) * a6 ^ 4 * g1 ^ 4 -
        (103219200 : K[X]) * a6 ^ 5 * g1 ^ 2 +
        (9175040 : K[X]) * a6 ^ 6)

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the nonsquare-chamber twelfth row
(`p₇ = H² g₂`, `H²⁴` peeled, `128 q₇ H` consumed): `q₁, …, q₆` sit at
`H¹⁶` here, i.e. at `H¹⁸` in the cleared row. -/
def alignedTwelfthNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(2061584302080 : K[X]) * a0 * a4 * H ^ 14 -
    (2061584302080 : K[X]) * a1 * a3 * H ^ 14 -
    (1030792151040 : K[X]) * a2 ^ 2 * H ^ 14 +
    (1649267441664 : K[X]) * a0 * b6 * H ^ 13 +
    (1374389534720 : K[X]) * a1 * b5 * H ^ 13 +
    (1099511627776 : K[X]) * a2 * b4 * H ^ 13 +
    (824633720832 : K[X]) * a3 * b3 * H ^ 13 +
    (549755813888 : K[X]) * a4 * b2 * H ^ 13 +
    (274877906944 : K[X]) * a5 * b1 * H ^ 13 -
    (515396075520 : K[X]) * a0 * a5 * g2 * H ^ 12 +
    (1288490188800 : K[X]) * a1 * a4 * g2 * H ^ 12 +
    (1288490188800 : K[X]) * a2 * a3 * g2 * H ^ 12 -
    (1236950581248 : K[X]) * a1 * b6 * g2 * H ^ 11 -
    (1030792151040 : K[X]) * a2 * b5 * g2 * H ^ 11 -
    (824633720832 : K[X]) * a3 * b4 * g2 * H ^ 11 -
    (618475290624 : K[X]) * a4 * b3 * g2 * H ^ 11 -
    (412316860416 : K[X]) * a5 * b2 * g2 * H ^ 11 -
    (206158430208 : K[X]) * b1 * a6 * g2 * H ^ 11 +
    (60129542144 : K[X]) * b1 * g2 ^ 3 * H ^ 11 -
    (257698037760 : K[X]) * a0 * a6 ^ 2 * H ^ 10 +
    (193273528320 : K[X]) * a0 * a6 * g2 ^ 2 * H ^ 10 -
    (28185722880 : K[X]) * a0 * g2 ^ 4 * H ^ 10 -
    (257698037760 : K[X]) * a1 * a5 * a6 * H ^ 10 +
    (418759311360 : K[X]) * a1 * a5 * g2 ^ 2 * H ^ 10 +
    (1546188226560 : K[X]) * a2 * a4 * a6 * H ^ 10 -
    (1159641169920 : K[X]) * a2 * a4 * g2 ^ 2 * H ^ 10 +
    (773094113280 : K[X]) * a3 ^ 2 * a6 * H ^ 10 -
    (579820584960 : K[X]) * a3 ^ 2 * g2 ^ 2 * H ^ 10 +
    (1803886264320 : K[X]) * a3 * a4 * a5 * H ^ 10 +
    (601295421440 : K[X]) * a4 ^ 3 * H ^ 10 -
    (1236950581248 : K[X]) * a2 * b6 * a6 * H ^ 9 +
    (1082331758592 : K[X]) * a2 * b6 * g2 ^ 2 * H ^ 9 -
    (1236950581248 : K[X]) * a3 * a5 * b6 * H ^ 9 -
    (1030792151040 : K[X]) * a3 * b5 * a6 * H ^ 9 +
    (901943132160 : K[X]) * a3 * b5 * g2 ^ 2 * H ^ 9 -
    (618475290624 : K[X]) * a4 ^ 2 * b6 * H ^ 9 -
    (1030792151040 : K[X]) * a4 * a5 * b5 * H ^ 9 -
    (824633720832 : K[X]) * a4 * b4 * a6 * H ^ 9 +
    (721554505728 : K[X]) * a4 * b4 * g2 ^ 2 * H ^ 9 -
    (412316860416 : K[X]) * a5 ^ 2 * b4 * H ^ 9 -
    (618475290624 : K[X]) * a5 * b3 * a6 * H ^ 9 +
    (541165879296 : K[X]) * a5 * b3 * g2 ^ 2 * H ^ 9 -
    (206158430208 : K[X]) * b2 * a6 ^ 2 * H ^ 9 +
    (360777252864 : K[X]) * b2 * a6 * g2 ^ 2 * H ^ 9 -
    (82678120448 : K[X]) * b2 * g2 ^ 4 * H ^ 9 +
    (225485783040 : K[X]) * a1 * a6 ^ 2 * g2 * H ^ 8 -
    (131533373440 : K[X]) * a1 * a6 * g2 ^ 3 * H ^ 8 +
    (15267266560 : K[X]) * a1 * g2 ^ 5 * H ^ 8 +
    (450971566080 : K[X]) * a2 * a5 * a6 * g2 * H ^ 8 -
    (319438192640 : K[X]) * a2 * a5 * g2 ^ 3 * H ^ 8 -
    (2705829396480 : K[X]) * a3 * a4 * a6 * g2 * H ^ 8 +
    (1127428915200 : K[X]) * a3 * a4 * g2 ^ 3 * H ^ 8 +
    (225485783040 : K[X]) * a3 * a5 ^ 2 * g2 * H ^ 8 -
    (1352914698240 : K[X]) * a4 ^ 2 * a5 * g2 * H ^ 8 +
    (2164663517184 : K[X]) * a3 * b6 * a6 * g2 * H ^ 7 -
    (992137445376 : K[X]) * a3 * b6 * g2 ^ 3 * H ^ 7 +
    (2164663517184 : K[X]) * a4 * a5 * b6 * g2 * H ^ 7 +
    (1803886264320 : K[X]) * a4 * b5 * a6 * g2 * H ^ 7 -
    (826781204480 : K[X]) * a4 * b5 * g2 ^ 3 * H ^ 7 +
    (901943132160 : K[X]) * a5 ^ 2 * b5 * g2 * H ^ 7 +
    (1443109011456 : K[X]) * a5 * b4 * a6 * g2 * H ^ 7 -
    (661424963584 : K[X]) * a5 * b4 * g2 ^ 3 * H ^ 7 +
    (541165879296 : K[X]) * b3 * a6 ^ 2 * g2 * H ^ 7 -
    (496068722688 : K[X]) * b3 * a6 * g2 ^ 3 * H ^ 7 +
    (93012885504 : K[X]) * b3 * g2 ^ 5 * H ^ 7 +
    (150323855360 : K[X]) * a2 * a6 ^ 3 * H ^ 6 -
    (225485783040 : K[X]) * a2 * a6 ^ 2 * g2 ^ 2 * H ^ 6 +
    (82208358400 : K[X]) * a2 * a6 * g2 ^ 4 * H ^ 6 -
    (6459228160 : K[X]) * a2 * g2 ^ 6 * H ^ 6 +
    (225485783040 : K[X]) * a3 * a5 * a6 ^ 2 * H ^ 6 -
    (620085903360 : K[X]) * a3 * a5 * a6 * g2 ^ 2 * H ^ 6 +
    (250148290560 : K[X]) * a3 * a5 * g2 ^ 4 * H ^ 6 -
    (676457349120 : K[X]) * a4 ^ 2 * a6 ^ 2 * H ^ 6 +
    (1860257710080 : K[X]) * a4 ^ 2 * a6 * g2 ^ 2 * H ^ 6 -
    (553144811520 : K[X]) * a4 ^ 2 * g2 ^ 4 * H ^ 6 -
    (394600120320 : K[X]) * a4 * a5 ^ 2 * g2 ^ 2 * H ^ 6 +
    (112742891520 : K[X]) * a5 ^ 4 * H ^ 6 +
    (1082331758592 : K[X]) * a4 * b6 * a6 ^ 2 * H ^ 5 -
    (2976412336128 : K[X]) * a4 * b6 * a6 * g2 ^ 2 * H ^ 5 +
    (930128855040 : K[X]) * a4 * b6 * g2 ^ 4 * H ^ 5 +
    (1082331758592 : K[X]) * a5 ^ 2 * b6 * a6 * H ^ 5 -
    (1488206168064 : K[X]) * a5 ^ 2 * b6 * g2 ^ 2 * H ^ 5 +
    (901943132160 : K[X]) * a5 * b5 * a6 ^ 2 * H ^ 5 -
    (2480343613440 : K[X]) * a5 * b5 * a6 * g2 ^ 2 * H ^ 5 +
    (775107379200 : K[X]) * a5 * b5 * g2 ^ 4 * H ^ 5 +
    (240518168576 : K[X]) * b4 * a6 ^ 3 * H ^ 5 -
    (992137445376 : K[X]) * b4 * a6 ^ 2 * g2 ^ 2 * H ^ 5 +
    (620085903360 : K[X]) * b4 * a6 * g2 ^ 4 * H ^ 5 -
    (98180268032 : K[X]) * b4 * g2 ^ 6 * H ^ 5 -
    (225485783040 : K[X]) * a3 * a6 ^ 3 * g2 * H ^ 4 +
    (183207198720 : K[X]) * a3 * a6 ^ 2 * g2 ^ 3 * H ^ 4 -
    (38755368960 : K[X]) * a3 * a6 * g2 ^ 5 * H ^ 4 +
    (346030080 : K[X]) * a3 * g2 ^ 7 * H ^ 4 -
    (450971566080 : K[X]) * a4 * a5 * a6 ^ 2 * g2 * H ^ 4 +
    (676457349120 : K[X]) * a4 * a5 * a6 * g2 ^ 3 * H ^ 4 -
    (193776844800 : K[X]) * a4 * a5 * g2 ^ 5 * H ^ 4 -
    (1522029035520 : K[X]) * a5 ^ 3 * a6 * g2 * H ^ 4 +
    (1068708659200 : K[X]) * a5 ^ 3 * g2 ^ 3 * H ^ 4 -
    (2976412336128 : K[X]) * a5 * b6 * a6 ^ 2 * g2 * H ^ 3 +
    (3720515420160 : K[X]) * a5 * b6 * a6 * g2 ^ 3 * H ^ 3 -
    (883622412288 : K[X]) * a5 * b6 * g2 ^ 5 * H ^ 3 -
    (826781204480 : K[X]) * b5 * a6 ^ 3 * g2 * H ^ 3 +
    (1550214758400 : K[X]) * b5 * a6 ^ 2 * g2 ^ 3 * H ^ 3 -
    (736352010240 : K[X]) * b5 * a6 * g2 ^ 5 * H ^ 3 +
    (100810096640 : K[X]) * b5 * g2 ^ 7 * H ^ 3 -
    (103347650560 : K[X]) * a4 * a6 ^ 4 * H ^ 2 +
    (258369126400 : K[X]) * a4 * a6 ^ 3 * g2 ^ 2 * H ^ 2 -
    (106577264640 : K[X]) * a4 * a6 ^ 2 * g2 ^ 4 * H ^ 2 -
    (807403520 : K[X]) * a4 * a6 * g2 ^ 6 * H ^ 2 +
    (4040622080 : K[X]) * a4 * g2 ^ 8 * H ^ 2 -
    (826781204480 : K[X]) * a5 ^ 2 * a6 ^ 3 * H ^ 2 +
    (4418112061440 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 ^ 2 * H ^ 2 -
    (3546116259840 : K[X]) * a5 ^ 2 * a6 * g2 ^ 4 * H ^ 2 +
    (689926307840 : K[X]) * a5 ^ 2 * g2 ^ 6 * H ^ 2 -
    (248034361344 : K[X]) * b6 * a6 ^ 4 * H +
    (1860257710080 : K[X]) * b6 * a6 ^ 3 * g2 ^ 2 * H -
    (2209056030720 : K[X]) * b6 * a6 ^ 2 * g2 ^ 4 * H +
    (846804811776 : K[X]) * b6 * a6 * g2 ^ 6 * H -
    (102070222848 : K[X]) * b6 * g2 ^ 8 * H +
    (1576051671040 : K[X]) * a5 * a6 ^ 4 * g2 -
    (4508541255680 : K[X]) * a5 * a6 ^ 3 * g2 ^ 3 +
    (3703559946240 : K[X]) * a5 * a6 ^ 2 * g2 ^ 5 -
    (1153289420800 : K[X]) * a5 * a6 * g2 ^ 7 +
    (120893358080 : K[X]) * a5 * g2 ^ 9 +
    Polynomial.C κ *
      (-(51539607552 : K[X]) * a0 * a6 * H ^ 13 -
        (51539607552 : K[X]) * a1 * a5 * H ^ 13 -
        (51539607552 : K[X]) * a2 * a4 * H ^ 13 -
        (25769803776 : K[X]) * a3 ^ 2 * H ^ 13 +
        (45097156608 : K[X]) * a1 * a6 * g2 * H ^ 11 -
        (1879048192 : K[X]) * a1 * g2 ^ 3 * H ^ 11 +
        (45097156608 : K[X]) * a2 * a5 * g2 * H ^ 11 +
        (45097156608 : K[X]) * a3 * a4 * g2 * H ^ 11 +
        (45097156608 : K[X]) * a2 * a6 ^ 2 * H ^ 9 -
        (45097156608 : K[X]) * a2 * a6 * g2 ^ 2 * H ^ 9 +
        (2583691264 : K[X]) * a2 * g2 ^ 4 * H ^ 9 +
        (90194313216 : K[X]) * a3 * a5 * a6 * H ^ 9 -
        (45097156608 : K[X]) * a3 * a5 * g2 ^ 2 * H ^ 9 +
        (45097156608 : K[X]) * a4 ^ 2 * a6 * H ^ 9 -
        (22548578304 : K[X]) * a4 ^ 2 * g2 ^ 2 * H ^ 9 +
        (45097156608 : K[X]) * a4 * a5 ^ 2 * H ^ 9 -
        (84557168640 : K[X]) * a3 * a6 ^ 2 * g2 * H ^ 7 +
        (46506442752 : K[X]) * a3 * a6 * g2 ^ 3 * H ^ 7 -
        (2906652672 : K[X]) * a3 * g2 ^ 5 * H ^ 7 -
        (169114337280 : K[X]) * a4 * a5 * a6 * g2 * H ^ 7 +
        (46506442752 : K[X]) * a4 * a5 * g2 ^ 3 * H ^ 7 -
        (28185722880 : K[X]) * a5 ^ 3 * g2 * H ^ 7 -
        (41339060224 : K[X]) * a4 * a6 ^ 3 * H ^ 5 +
        (124017180672 : K[X]) * a4 * a6 ^ 2 * g2 ^ 2 * H ^ 5 -
        (48444211200 : K[X]) * a4 * a6 * g2 ^ 4 * H ^ 5 +
        (3068133376 : K[X]) * a4 * g2 ^ 6 * H ^ 5 -
        (62008590336 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 5 +
        (124017180672 : K[X]) * a5 ^ 2 * a6 * g2 ^ 2 * H ^ 5 -
        (24222105600 : K[X]) * a5 ^ 2 * g2 ^ 4 * H ^ 5 +
        (118849798144 : K[X]) * a5 * a6 ^ 3 * g2 * H ^ 3 -
        (164710318080 : K[X]) * a5 * a6 ^ 2 * g2 ^ 3 * H ^ 3 +
        (50624200704 : K[X]) * a5 * a6 * g2 ^ 5 * H ^ 3 -
        (3150315520 : K[X]) * a5 * g2 ^ 7 * H ^ 3 +
        (7751073792 : K[X]) * a6 ^ 5 * H -
        (58133053440 : K[X]) * a6 ^ 4 * g2 ^ 2 * H +
        (69033000960 : K[X]) * a6 ^ 3 * g2 ^ 4 * H -
        (26462650368 : K[X]) * a6 ^ 2 * g2 ^ 6 * H +
        (3189694464 : K[X]) * a6 * g2 ^ 8 * H)

/-- Cleared twelfth row of the nonsquare chamber, in factored form:
`H²` times the transport co-factor plus the pure `g₂, p₆` dodecic
block. -/
def alignedTwelfthNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedTwelfthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ +
    (7040 : K[X]) *
      ((853461 : K[X]) * g2 ^ 12 - (12270960 : K[X]) * a6 * g2 ^ 10 +
        (67374912 : K[X]) * a6 ^ 2 * g2 ^ 8 -
        (175142912 : K[X]) * a6 ^ 3 * g2 ^ 6 +
        (214609920 : K[X]) * a6 ^ 4 * g2 ^ 4 -
        (103219200 : K[X]) * a6 ^ 5 * g2 ^ 2 +
        (9175040 : K[X]) * a6 ^ 6)

/-! ## Square chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀⁴⁸` from `N₁₂ = κ₁₁ H⁴²` on `H = h₀²`, `p₇ = h₀⁴ g₁`
and consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `-11274289152 p₀ g₁ h₀²⁴ + 9865003008 p₁ g₁² h₀²⁰
- 11274289152 p₁ p₆ h₀²⁰ - 11274289152 p₂ p₅ h₀²⁰ - 11274289152 p₃ p₄ h₀²⁰
- 9042919424 p₂ g₁³ h₀¹⁶ + 19730006016 p₂ p₆ g₁ h₀¹⁶
+ 19730006016 p₃ p₅ g₁ h₀¹⁶ + 9865003008 p₄² g₁ h₀¹⁶ + …
+ 801115392 g₁⁹ - 7442620416 g₁⁷ p₆ + 23154819072 g₁⁵ p₆²
- 26846167040 g₁³ p₆³ + 8477736960 g₁ p₆⁴`, leaves the cleared twelfth
row of the square chamber together with its factored transport form.
Nothing is forced: `κ₁₁` is preserved, not cleared. -/
theorem alignedSquareTwelfth_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₁ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hN : alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₁₁ * H ^ 42)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedTwelfthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
        b5 b6 κ μ =
      Polynomial.C κ₁₁ * h0 ^ 36 ∧
    (7040 : K[X]) *
        ((853461 : K[X]) * g1 ^ 12 - (12270960 : K[X]) * a6 * g1 ^ 10 +
          (67374912 : K[X]) * a6 ^ 2 * g1 ^ 8 -
          (175142912 : K[X]) * a6 ^ 3 * g1 ^ 6 +
          (214609920 : K[X]) * a6 ^ 4 * g1 ^ 4 -
          (103219200 : K[X]) * a6 ^ 5 * g1 ^ 2 +
          (9175040 : K[X]) * a6 ^ 6) =
      h0 ^ 4 *
        (Polynomial.C κ₁₁ * h0 ^ 32 -
          alignedTwelfthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2
            b3 b4 b5 b6 κ μ) := by
  have hN' := hN
  simp only [alignedTwelfthDefect810, hHsq, hg] at hN'
  have hclear :
      alignedTwelfthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ μ =
        Polynomial.C κ₁₁ * h0 ^ 36 := by
    simp only [alignedTwelfthSquareRow810, alignedTwelfthSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 48 hh0)
    linear_combination hN' -
      h0 ^ 48 *
        (-(11274289152 : K[X]) * a0 * g1 * h0 ^ 24 -
          (11274289152 : K[X]) * a1 * a6 * h0 ^ 20 +
          (9865003008 : K[X]) * a1 * g1 ^ 2 * h0 ^ 20 -
          (11274289152 : K[X]) * a2 * a5 * h0 ^ 20 -
          (11274289152 : K[X]) * a3 * a4 * h0 ^ 20 +
          (19730006016 : K[X]) * a2 * a6 * g1 * h0 ^ 16 -
          (9042919424 : K[X]) * a2 * g1 ^ 3 * h0 ^ 16 +
          (19730006016 : K[X]) * a3 * a5 * g1 * h0 ^ 16 +
          (9865003008 : K[X]) * a4 ^ 2 * g1 * h0 ^ 16 +
          (9865003008 : K[X]) * a3 * a6 ^ 2 * h0 ^ 12 -
          (27128758272 : K[X]) * a3 * a6 * g1 ^ 2 * h0 ^ 12 +
          (8477736960 : K[X]) * a3 * g1 ^ 4 * h0 ^ 12 +
          (19730006016 : K[X]) * a4 * a5 * a6 * h0 ^ 12 -
          (27128758272 : K[X]) * a4 * a5 * g1 ^ 2 * h0 ^ 12 +
          (3288334336 : K[X]) * a5 ^ 3 * h0 ^ 12 -
          (27128758272 : K[X]) * a4 * a6 ^ 2 * g1 * h0 ^ 8 +
          (33910947840 : K[X]) * a4 * a6 * g1 ^ 3 * h0 ^ 8 -
          (8053850112 : K[X]) * a4 * g1 ^ 5 * h0 ^ 8 -
          (27128758272 : K[X]) * a5 ^ 2 * a6 * g1 * h0 ^ 8 +
          (16955473920 : K[X]) * a5 ^ 2 * g1 ^ 3 * h0 ^ 8 -
          (9042919424 : K[X]) * a5 * a6 ^ 3 * h0 ^ 4 +
          (50866421760 : K[X]) * a5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 4 -
          (40269250560 : K[X]) * a5 * a6 * g1 ^ 4 * h0 ^ 4 +
          (7718273024 : K[X]) * a5 * g1 ^ 6 * h0 ^ 4 +
          (8477736960 : K[X]) * a6 ^ 4 * g1 -
          (26846167040 : K[X]) * a6 ^ 3 * g1 ^ 3 +
          (23154819072 : K[X]) * a6 ^ 2 * g1 ^ 5 -
          (7442620416 : K[X]) * a6 * g1 ^ 7 +
          (801115392 : K[X]) * g1 ^ 9) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedTwelfthSquareRow810] at hclear
  linear_combination hclear

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `H²⁴` from `N₁₂ = κ₁₁ H⁴²` on `p₇ = H² g₂` and consuming
the previous factored quotient (`128 q₇ H` solved) with the same mate,
leaves the cleared twelfth row of the nonsquare chamber together with
its factored transport form.  The unsquared integral forces nothing:
`κ₁₁` is preserved, not cleared. -/
theorem alignedNonsquareTwelfth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₁ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hN : alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₁₁ * H ^ 42)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedTwelfthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ =
      Polynomial.C κ₁₁ * H ^ 18 ∧
    (7040 : K[X]) *
        ((853461 : K[X]) * g2 ^ 12 - (12270960 : K[X]) * a6 * g2 ^ 10 +
          (67374912 : K[X]) * a6 ^ 2 * g2 ^ 8 -
          (175142912 : K[X]) * a6 ^ 3 * g2 ^ 6 +
          (214609920 : K[X]) * a6 ^ 4 * g2 ^ 4 -
          (103219200 : K[X]) * a6 ^ 5 * g2 ^ 2 +
          (9175040 : K[X]) * a6 ^ 6) =
      H ^ 2 *
        (Polynomial.C κ₁₁ * H ^ 16 -
          alignedTwelfthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1
            b2 b3 b4 b5 b6 κ) := by
  have hN' := hN
  simp only [alignedTwelfthDefect810, hg2] at hN'
  have hclear :
      alignedTwelfthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ =
        Polynomial.C κ₁₁ * H ^ 18 := by
    simp only [alignedTwelfthNonsquareRow810,
      alignedTwelfthNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 24 hH)
    linear_combination hN' -
      H ^ 24 *
        (-(11274289152 : K[X]) * a0 * g2 * H ^ 12 -
          (11274289152 : K[X]) * a1 * a6 * H ^ 10 +
          (9865003008 : K[X]) * a1 * g2 ^ 2 * H ^ 10 -
          (11274289152 : K[X]) * a2 * a5 * H ^ 10 -
          (11274289152 : K[X]) * a3 * a4 * H ^ 10 +
          (19730006016 : K[X]) * a2 * a6 * g2 * H ^ 8 -
          (9042919424 : K[X]) * a2 * g2 ^ 3 * H ^ 8 +
          (19730006016 : K[X]) * a3 * a5 * g2 * H ^ 8 +
          (9865003008 : K[X]) * a4 ^ 2 * g2 * H ^ 8 +
          (9865003008 : K[X]) * a3 * a6 ^ 2 * H ^ 6 -
          (27128758272 : K[X]) * a3 * a6 * g2 ^ 2 * H ^ 6 +
          (8477736960 : K[X]) * a3 * g2 ^ 4 * H ^ 6 +
          (19730006016 : K[X]) * a4 * a5 * a6 * H ^ 6 -
          (27128758272 : K[X]) * a4 * a5 * g2 ^ 2 * H ^ 6 +
          (3288334336 : K[X]) * a5 ^ 3 * H ^ 6 -
          (27128758272 : K[X]) * a4 * a6 ^ 2 * g2 * H ^ 4 +
          (33910947840 : K[X]) * a4 * a6 * g2 ^ 3 * H ^ 4 -
          (8053850112 : K[X]) * a4 * g2 ^ 5 * H ^ 4 -
          (27128758272 : K[X]) * a5 ^ 2 * a6 * g2 * H ^ 4 +
          (16955473920 : K[X]) * a5 ^ 2 * g2 ^ 3 * H ^ 4 -
          (9042919424 : K[X]) * a5 * a6 ^ 3 * H ^ 2 +
          (50866421760 : K[X]) * a5 * a6 ^ 2 * g2 ^ 2 * H ^ 2 -
          (40269250560 : K[X]) * a5 * a6 * g2 ^ 4 * H ^ 2 +
          (7718273024 : K[X]) * a5 * g2 ^ 6 * H ^ 2 +
          (8477736960 : K[X]) * a6 ^ 4 * g2 -
          (26846167040 : K[X]) * a6 ^ 3 * g2 ^ 3 +
          (23154819072 : K[X]) * a6 ^ 2 * g2 ^ 5 -
          (7442620416 : K[X]) * a6 * g2 ^ 7 +
          (801115392 : K[X]) * g2 ^ 9) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedTwelfthNonsquareRow810] at hclear
  linear_combination hclear

/-! ## Source-facing twelfth-row packets -/

/-- Source-facing weight-eighty-four integral of a normalized aligned
scale-two `(8,10)` source: the degree-`5` row is consumed into
`N₁₂ = κ₁₁ H⁴²` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedTwelfthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ : K),
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
          Polynomial.C κ₁₁ * H ^ 42 := by
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
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀, κ₁₁,
    aligned_q9_solved_810 haligned, hM, hE4, hF2, hG, hI2, hJ, hL2,
    hN10, hN11, hN12⟩

/-- Exact square-chamber twelfth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`5`
row gives the cleared twelfth row (with `q₁, …, q₆` at `h₀³⁶`) against
the preserved `κ₁₁`, the carried root collapse `g₁ = p₆ = 0`, and the
carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedTwelfthFace_squareChamber_packet
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
    ∃ (κ μ κ₁₁ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        alignedTwelfthSquareRow810 h0 g1 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ μ =
          Polynomial.C κ₁₁ * h0 ^ 36 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 42 := by
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
  obtain ⟨κ₁₁, hNrel⟩ :=
    alignedTwelfthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hsolved12, _hfact12⟩ :=
    alignedSquareTwelfth_solved_810 hh0 hHsq hp7 hNrel hcore
  exact ⟨κ, μ, κ₁₁, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hsolved12,
    hcollapse, hdvdg1, hdvdp6, hNrel⟩

/-- Exact nonsquare-chamber twelfth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂` and the previous
packet, the consumed degree-`5` row gives the cleared twelfth row
(with `q₁, …, q₆` at `H¹⁸`) against the preserved `κ₁₁`, the carried
root collapse `g₂ = p₆ = 0` at every (simple) root of the core, and
the carried descents `H ∣ g₂`, `H ∣ p₆`.  The unsquared integral
forces nothing: `κ₁₁` is not cleared. -/
theorem normalized810ScaleTwo_alignedTwelfthFace_nonsquareChamber_packet
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
    ∃ (κ κ₁₁ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        alignedTwelfthNonsquareRow810 H g2 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ =
          Polynomial.C κ₁₁ * H ^ 18 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedTwelfthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₁₁ * H ^ 42 := by
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
  obtain ⟨κ₁₁, hNrel⟩ :=
    alignedTwelfthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hclear12, _hfact12⟩ :=
    alignedNonsquareTwelfth_solved_810 hH hg2 hNrel hfac
  exact ⟨κ, κ₁₁, g2, hg2, by rw [hq9, hg2]; ring, hclear12,
    hcollapse, hdvdg2, hdvdp6, hNrel⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`5`
aligned row, carrying the factored transport of the dodecic block.
Neither chamber is excluded, the constants `κ`, `μ`, `κ₁₁` are
preserved (nothing is forced by the unsquared integral), and no
closure is claimed. -/
theorem normalized810ScaleTwo_alignedTwelfthFace_chamberDichotomy
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
      ∃ (κ μ κ₁₁ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (7040 : K[X]) *
              ((853461 : K[X]) * g1 ^ 12 -
                (12270960 : K[X]) * p.coeff 6 * g1 ^ 10 +
                (67374912 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 8 -
                (175142912 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 6 +
                (214609920 : K[X]) * p.coeff 6 ^ 4 * g1 ^ 4 -
                (103219200 : K[X]) * p.coeff 6 ^ 5 * g1 ^ 2 +
                (9175040 : K[X]) * p.coeff 6 ^ 6) =
            h0 ^ 4 *
              (Polynomial.C κ₁₁ * h0 ^ 32 -
                alignedTwelfthSquareCof810 h0 g1 (p.coeff 0) (p.coeff 1)
                  (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
                  (p.coeff 6) (q.coeff 1) (q.coeff 2) (q.coeff 3)
                  (q.coeff 4) (q.coeff 5) (q.coeff 6) κ μ) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₁₁ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (7040 : K[X]) *
              ((853461 : K[X]) * g2 ^ 12 -
                (12270960 : K[X]) * p.coeff 6 * g2 ^ 10 +
                (67374912 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 8 -
                (175142912 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 6 +
                (214609920 : K[X]) * p.coeff 6 ^ 4 * g2 ^ 4 -
                (103219200 : K[X]) * p.coeff 6 ^ 5 * g2 ^ 2 +
                (9175040 : K[X]) * p.coeff 6 ^ 6) =
            H ^ 2 *
              (Polynomial.C κ₁₁ * H ^ 16 -
                alignedTwelfthNonsquareCof810 H g2 (p.coeff 0)
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
      normalized810ScaleTwo_alignedTwelfthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₁₁, g1, hp7, hq9, hsolved12,
      hcollapse, hdvdg1, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₁₁, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedTwelfthSquareRow810] at hsolved12
    linear_combination hsolved12
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedTwelfthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₁₁, g2, hp7, hq9, hclear12, hcollapse,
      hdvdg2, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, κ₁₁, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedTwelfthNonsquareRow810] at hclear12
    linear_combination hclear12

/-- Chamber-independent root jet after the consumed degree-`5` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its dodecic content is absorbed by the
degree-`13` collapse (`alignedTwelfth_rootDodecic_absorbed_810`) — and
no new coefficient occurs, so the row re-ties `q₁, …, q₆` into the
cleared twelfth row instead of killing anything new at the root. -/
theorem normalized810ScaleTwo_alignedTwelfthFace_rootJet
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
  normalized810ScaleTwo_alignedEleventhFace_rootJet hsource haligned

#print axioms alignedTwelfthCoefficientJacobianRow_810
#print axioms alignedTwelfthDefect_weightedDerivative_identity_810
#print axioms alignedTwelfthDefectRow_eq_zero_810
#print axioms alignedTwelfthDefectPowerRelation_810
#print axioms alignedTwelfth_factored_rootDodecic_810
#print axioms alignedTwelfth_rootDodecic_absorbed_810
#print axioms alignedSquareTwelfth_solved_810
#print axioms alignedNonsquareTwelfth_solved_810
#print axioms normalized810ScaleTwo_alignedTwelfthFace_packet
#print axioms normalized810ScaleTwo_alignedTwelfthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedTwelfthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedTwelfthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedTwelfthFace_rootJet

end Max11DegreeRoutes
