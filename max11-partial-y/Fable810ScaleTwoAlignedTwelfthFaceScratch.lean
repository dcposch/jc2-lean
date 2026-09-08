import Fable810ScaleTwoAlignedEleventhFaceScratch

/-! # Twelfth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedEleventhFaceScratch` consumed the degree-`5`
aligned Keller row (the chamber-free `N₁₂ = κ₁₁ H⁴²`).  This file
consumes the next unused aligned row, the degree-`4` Jacobian
coefficient (internal names `alignedThirteenth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9`/`8`/`7`/`6`/`5` rows
`2 H D' - 21 D H' = 0`, `H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`,
`H G' - 21 G H' = 0`, `2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`,
`2 H L' - 63 L H' = 0`, `H N₁₀' - 35 N₁₀ H' = 0`,
`2 H N₁₁' - 77 N₁₁ H' = 0`, `H N₁₂' - 42 N₁₂ H' = 0`, the degree-`4`
row is the weighted derivative of the weight-ninety-one defect

`N₁₃ = -27487790694400 p₀ p₃ H⁴⁴ - 27487790694400 p₁ p₂ H⁴⁴
  + 21990232555520 p₀ q₅ H⁴³ + 17592186044416 p₁ q₄ H⁴³
  + 13194139533312 p₂ q₃ H⁴³ + 8796093022208 p₃ q₂ H⁴³
  + 4398046511104 p₄ q₁ H⁴³ + … - 92154224085 p₇¹³
  + κ (-687194767360 p₀ p₅ H⁴³ - 687194767360 p₁ p₄ H⁴³
       - 687194767360 p₂ p₃ H⁴³ + … + 29042543348 p₇¹¹ H⁷)`

(the full two-hundred-seventy-term expression is the literal body of
`alignedThirteenthDefect810`; the defect is `q₀`-free — all three
weight-ninety-one `q₀`-ansatz monomials `q₀ p₅ H⁴³`, `q₀ p₆ p₇ H³⁹`,
`q₀ p₇³ H³⁵` solve to zero — and `q₀` enters the multiplier identity
only through the `N₁₀`-row correction
`40960 p₅ H⁸ (H N₁₀' - 35 N₁₀ H')`), via the exact multiplier identity

`8796093022208 H⁴⁴ · row₄ = (2 H N₁₃' - 91 N₁₃ H')
  + (150323855360 p₀ p₆ H³² + 150323855360 p₁ p₅ H³²
     + 150323855360 p₂ p₄ H³² + 75161927680 p₃² H³² - …
     - 35689885 p₇¹⁰) (2 H D' - 21 D H')
  + (16106127360 p₀ p₇ H²⁸ + 16106127360 p₁ p₆ H²⁸
     + 16106127360 p₂ p₅ H²⁸ + 16106127360 p₃ p₄ H²⁸ - …
     - 14144000 p₇⁹) (H E' - 14 E H')
  + (1342177280 p₀ H²⁸ + 838860800 p₁ p₇ H²⁴ + 838860800 p₂ p₆ H²⁴
     + 838860800 p₃ p₅ H²⁴ + … + 2022075 p₇⁸) (2 H F' - 35 F H')
  + (671088640 p₁ H²⁴ + 335544320 p₂ p₇ H²⁰ + 335544320 p₃ p₆ H²⁰
     + 335544320 p₄ p₅ H²⁰ - … - 1966080 p₇⁷) (H G' - 21 G H')
  + (5242880 p₂ H²⁰ + 1966080 p₃ p₇ H¹⁶ + 1966080 p₄ p₆ H¹⁶
     + 983040 p₅² H¹⁶ - … - 26390 p₇⁶) (2 H I' - 49 I H')
  + (1310720 p₃ H¹⁶ + 327680 p₄ p₇ H¹² + 327680 p₅ p₆ H¹²
     - 122880 p₅ p₇² H⁸ - … - 9856 p₇⁵) (H J' - 28 J H')
  + (40960 p₄ H¹² + 5120 p₅ p₇ H⁸ + 2560 p₆² H⁸ - 2240 p₆ p₇² H⁴
     + 350 p₇⁴) (2 H L' - 63 L H')
  + 40960 p₅ H⁸ (H N₁₀' - 35 N₁₀ H')
  + (80 p₆ H⁴ - 5 p₇²) (2 H N₁₁' - 77 N₁₁ H')
  + 20 p₇ (H N₁₂' - 42 N₁₂ H')`.

The row sees only `q₀, …, q₅`, so — as on the previous two faces — no
`N`- and no `C`-correction occurs at all: every correction is a
consumed tower row, and for the first time *three* integral-tower rows
(`N₁₀`, `N₁₁` and `N₁₂`) correct simultaneously (the `N₁₀`-multiplier
degenerates to the single monomial `40960 p₅ H⁸`).  On the aligned
face every right-hand correction vanishes, so `2 H N₁₃' = 91 N₁₃ H'`
and the squared weight-ninety-one first integral

`N₁₃² = κ₁₂ H⁹¹`

holds for a preserved constant `κ₁₂`.  The exponent is odd, so —
exactly as for the degree-`14`, degree-`12`, degree-`10`, degree-`8`,
and degree-`6` rows — the integral is **chambered**:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: `N₁₃ = ν₅ h₀⁹¹` with
  `ν₅² = κ₁₂`; peeling `h₀⁵²` and consuming the previous factored
  quotient (`128 q₇ h₀²` solved, transported by the mate
  `-150323855360 p₀ p₆ h₀²⁴ + 122138132480 p₀ g₁² h₀²⁴
  - 150323855360 p₁ p₅ h₀²⁴ - 150323855360 p₂ p₄ h₀²⁴
  - 75161927680 p₃² h₀²⁴ - 106870865920 p₁ g₁³ h₀²⁰ + …
  - 7260635837 g₁¹⁰`) leaves the cleared thirteenth row
  `alignedThirteenthSquareRow810` (with `q₁, …, q₆` re-tied into the
  weight-thirty-nine level) against `ν₅ h₀³⁹`, and the factored
  transport `2900 g₁ (19258981 g₁¹² - 298574016 p₆ g₁¹⁰
  + 1809391168 p₆² g₁⁸ - 5384491008 p₆³ g₁⁶ + 8054079488 p₆⁴ g₁⁴
  - 5438963712 p₆⁵ g₁² + 1145044992 p₆⁶) = h₀⁴ (co-factor - ν₅ h₀³⁵)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₁₂ = 0` and `N₁₃ ≡ 0`.  With `p₇ = H² g₂`, peeling
  `H²⁶` and consuming the previous factored quotient (same mate) leaves
  the cleared thirteenth row `alignedThirteenthNonsquareRow810` equal
  to zero and the transport `2900 g₂ (19258981 g₂¹² - 298574016 p₆ g₂¹⁰
  + 1809391168 p₆² g₂⁸ - 5384491008 p₆³ g₂⁶ + 8054079488 p₆⁴ g₂⁴
  - 5438963712 p₆⁵ g₂² + 1145044992 p₆⁶) = H² · co-factor`.

At a root of the transport co-factor the honest root branch is the
root tridecic `g = 0 ∨ 19258981 g¹² - 298574016 p₆ g¹⁰
+ 1809391168 p₆² g⁸ - 5384491008 p₆³ g⁶ + 8054079488 p₆⁴ g⁴
- 5438963712 p₆⁵ g² + 1145044992 p₆⁶ = 0` — the even dodecic core has
a pure `p₆⁶` tail, exactly as on the degree-`5` face.  Like the
quartic through dodecic of the previous rows it adds *no new* root
information: the consumed degree-`13` row already collapsed
`g(a) = 0 ∧ p₆(a) = 0` at every core root, and that collapse absorbs
the tridecic identically
(`alignedThirteenth_rootTridecic_absorbed_810`).  The
chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` — the
row re-ties `q₁, …, q₆` into the cleared thirteenth row (at `h₀³⁹`,
resp. into the vanished nonsquare row) without killing anything new at
the root.

No closure is claimed.  Both chambers remain open where not forced
(`κ₁₂ = 0` and `N₁₃ ≡ 0` are forced in the nonsquare chamber only,
exactly as `κ₈ = 0` and `κ₁₀ = 0` were), the constants `κ`, `μ`,
`κ₃`, `κ₄`, `κ₅`, `κ₆`, `κ₇`, `κ₈`, `κ₉`, `κ₁₀`, `κ₁₁`, and the new
`κ₁₂ = ν₅²` are preserved where not forced, the zero branches
(`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`,
`κ₆ = 0`, `κ₇ = 0`, `κ₈ = 0` in the square chamber, `κ₉ = 0`,
`κ₁₀ = 0` in the square chamber, `κ₁₁ = 0`, `κ₁₂ = 0` in the square
chamber, `ν₅ = 0`) are not excluded as polynomial identities, the
deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H` from the
degree-`13` face are still not re-cleared through the tower here, the
root tridecic is recorded but not excluded as an identity, and no
individual vanishing of `p₀`, `p₁`, `p₂`, `p₃`, `p₄`, `p₅`, `q₀`,
`q₁`, `q₂`, `q₃`, `q₄`, `q₅`, `q₆`, `q₇` is claimed.  The next unused
Keller row on the aligned face is the degree-`3` Jacobian coefficient
(weight-ninety-eight defect, even exponent, hence chamber-free).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal degree-`4` Keller coefficient on the aligned face -/

/-- The thirteenth row below the leading weighted-Wronskian row for
outer degrees `(8,10)`: the degree-`4` Jacobian coefficient. -/
theorem alignedThirteenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

/-! ## Aligned thirteenth defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-ninety-one defect of the degree-`4` aligned `(8,10)` row.
On the aligned face its square is a polynomial first integral of odd
weight ninety-one, hence chambered.  The defect is `q₀`-free. -/
def alignedThirteenthDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    K[X] :=
    -(27487790694400 : K[X]) * a0 * a3 * H ^ 44 -
    (27487790694400 : K[X]) * a1 * a2 * H ^ 44 +
    (21990232555520 : K[X]) * a0 * b5 * H ^ 43 +
    (17592186044416 : K[X]) * a1 * b4 * H ^ 43 +
    (13194139533312 : K[X]) * a2 * b3 * H ^ 43 +
    (8796093022208 : K[X]) * a3 * b2 * H ^ 43 +
    (4398046511104 : K[X]) * a4 * b1 * H ^ 43 +
    (13743895347200 : K[X]) * a0 * a4 * a7 * H ^ 40 +
    (17179869184000 : K[X]) * a0 * a5 * a6 * H ^ 40 +
    (13743895347200 : K[X]) * a1 * a3 * a7 * H ^ 40 +
    (17179869184000 : K[X]) * a1 * a4 * a6 * H ^ 40 +
    (22333829939200 : K[X]) * a1 * a5 ^ 2 * H ^ 40 +
    (6871947673600 : K[X]) * a2 ^ 2 * a7 * H ^ 40 +
    (17179869184000 : K[X]) * a2 * a3 * a6 * H ^ 40 +
    (44667659878400 : K[X]) * a2 * a4 * a5 * H ^ 40 +
    (22333829939200 : K[X]) * a3 ^ 2 * a5 * H ^ 40 +
    (22333829939200 : K[X]) * a3 * a4 ^ 2 * H ^ 40 -
    (19241453486080 : K[X]) * a0 * b7 * a6 * H ^ 39 -
    (16492674416640 : K[X]) * a0 * b6 * a7 * H ^ 39 -
    (19241453486080 : K[X]) * a1 * a5 * b7 * H ^ 39 -
    (16492674416640 : K[X]) * a1 * b6 * a6 * H ^ 39 -
    (13743895347200 : K[X]) * a1 * b5 * a7 * H ^ 39 -
    (19241453486080 : K[X]) * a2 * a4 * b7 * H ^ 39 -
    (16492674416640 : K[X]) * a2 * a5 * b6 * H ^ 39 -
    (13743895347200 : K[X]) * a2 * b5 * a6 * H ^ 39 -
    (10995116277760 : K[X]) * a2 * b4 * a7 * H ^ 39 -
    (9620726743040 : K[X]) * a3 ^ 2 * b7 * H ^ 39 -
    (16492674416640 : K[X]) * a3 * a4 * b6 * H ^ 39 -
    (13743895347200 : K[X]) * a3 * a5 * b5 * H ^ 39 -
    (10995116277760 : K[X]) * a3 * b4 * a6 * H ^ 39 -
    (8246337208320 : K[X]) * a3 * b3 * a7 * H ^ 39 -
    (6871947673600 : K[X]) * a4 ^ 2 * b5 * H ^ 39 -
    (10995116277760 : K[X]) * a4 * a5 * b4 * H ^ 39 -
    (8246337208320 : K[X]) * a4 * b3 * a6 * H ^ 39 -
    (5497558138880 : K[X]) * a4 * b2 * a7 * H ^ 39 -
    (4123168604160 : K[X]) * a5 ^ 2 * b3 * H ^ 39 -
    (5497558138880 : K[X]) * a5 * b2 * a6 * H ^ 39 -
    (2748779069440 : K[X]) * a5 * b1 * a7 * H ^ 39 -
    (1374389534720 : K[X]) * b1 * a6 ^ 2 * H ^ 39 -
    (11811160064000 : K[X]) * a0 * a5 * a7 ^ 2 * H ^ 36 +
    (11166914969600 : K[X]) * a0 * a6 ^ 2 * a7 * H ^ 36 -
    (11811160064000 : K[X]) * a1 * a4 * a7 ^ 2 * H ^ 36 -
    (22333829939200 : K[X]) * a1 * a5 * a6 * a7 * H ^ 36 +
    (2791728742400 : K[X]) * a1 * a6 ^ 3 * H ^ 36 -
    (11811160064000 : K[X]) * a2 * a3 * a7 ^ 2 * H ^ 36 -
    (22333829939200 : K[X]) * a2 * a4 * a6 * a7 * H ^ 36 -
    (33500744908800 : K[X]) * a2 * a5 ^ 2 * a7 * H ^ 36 -
    (13958643712000 : K[X]) * a2 * a5 * a6 ^ 2 * H ^ 36 -
    (11166914969600 : K[X]) * a3 ^ 2 * a6 * a7 * H ^ 36 -
    (67001489817600 : K[X]) * a3 * a4 * a5 * a7 * H ^ 36 -
    (13958643712000 : K[X]) * a3 * a4 * a6 ^ 2 * H ^ 36 -
    (36292473651200 : K[X]) * a3 * a5 ^ 2 * a6 * H ^ 36 -
    (11166914969600 : K[X]) * a4 ^ 3 * a7 * H ^ 36 -
    (36292473651200 : K[X]) * a4 ^ 2 * a5 * a6 * H ^ 36 -
    (19542101196800 : K[X]) * a4 * a5 ^ 3 * H ^ 36 +
    (15633680957440 : K[X]) * a0 * b7 * a7 ^ 2 * H ^ 35 +
    (31267361914880 : K[X]) * a1 * b7 * a6 * a7 * H ^ 35 +
    (13400297963520 : K[X]) * a1 * b6 * a7 ^ 2 * H ^ 35 +
    (31267361914880 : K[X]) * a2 * a5 * b7 * a7 * H ^ 35 +
    (15633680957440 : K[X]) * a2 * b7 * a6 ^ 2 * H ^ 35 +
    (26800595927040 : K[X]) * a2 * b6 * a6 * a7 * H ^ 35 +
    (11166914969600 : K[X]) * a2 * b5 * a7 ^ 2 * H ^ 35 +
    (31267361914880 : K[X]) * a3 * a4 * b7 * a7 * H ^ 35 +
    (31267361914880 : K[X]) * a3 * a5 * b7 * a6 * H ^ 35 +
    (26800595927040 : K[X]) * a3 * a5 * b6 * a7 * H ^ 35 +
    (13400297963520 : K[X]) * a3 * b6 * a6 ^ 2 * H ^ 35 +
    (22333829939200 : K[X]) * a3 * b5 * a6 * a7 * H ^ 35 +
    (8933531975680 : K[X]) * a3 * b4 * a7 ^ 2 * H ^ 35 +
    (15633680957440 : K[X]) * a4 ^ 2 * b7 * a6 * H ^ 35 +
    (13400297963520 : K[X]) * a4 ^ 2 * b6 * a7 * H ^ 35 +
    (15633680957440 : K[X]) * a4 * a5 ^ 2 * b7 * H ^ 35 +
    (26800595927040 : K[X]) * a4 * a5 * b6 * a6 * H ^ 35 +
    (22333829939200 : K[X]) * a4 * a5 * b5 * a7 * H ^ 35 +
    (11166914969600 : K[X]) * a4 * b5 * a6 ^ 2 * H ^ 35 +
    (17867063951360 : K[X]) * a4 * b4 * a6 * a7 * H ^ 35 +
    (6700148981760 : K[X]) * a4 * b3 * a7 ^ 2 * H ^ 35 +
    (4466765987840 : K[X]) * a5 ^ 3 * b6 * H ^ 35 +
    (11166914969600 : K[X]) * a5 ^ 2 * b5 * a6 * H ^ 35 +
    (8933531975680 : K[X]) * a5 ^ 2 * b4 * a7 * H ^ 35 +
    (8933531975680 : K[X]) * a5 * b4 * a6 ^ 2 * H ^ 35 +
    (13400297963520 : K[X]) * a5 * b3 * a6 * a7 * H ^ 35 +
    (4466765987840 : K[X]) * a5 * b2 * a7 ^ 2 * H ^ 35 +
    (2233382993920 : K[X]) * b3 * a6 ^ 3 * H ^ 35 +
    (4466765987840 : K[X]) * b2 * a6 ^ 2 * a7 * H ^ 35 +
    (2233382993920 : K[X]) * b1 * a6 * a7 ^ 2 * H ^ 35 -
    (9073118412800 : K[X]) * a0 * a6 * a7 ^ 3 * H ^ 32 +
    (10468982784000 : K[X]) * a1 * a5 * a7 ^ 3 * H ^ 32 -
    (15528991129600 : K[X]) * a1 * a6 ^ 2 * a7 ^ 2 * H ^ 32 +
    (10468982784000 : K[X]) * a2 * a4 * a7 ^ 3 * H ^ 32 +
    (27568321331200 : K[X]) * a2 * a5 * a6 * a7 ^ 2 * H ^ 32 -
    (9771050598400 : K[X]) * a2 * a6 ^ 3 * a7 * H ^ 32 +
    (5234491392000 : K[X]) * a3 ^ 2 * a7 ^ 3 * H ^ 32 +
    (27568321331200 : K[X]) * a3 * a4 * a6 * a7 ^ 2 * H ^ 32 +
    (43097312460800 : K[X]) * a3 * a5 ^ 2 * a7 ^ 2 * H ^ 32 +
    (29313151795200 : K[X]) * a3 * a5 * a6 ^ 2 * a7 * H ^ 32 -
    (1832071987200 : K[X]) * a3 * a6 ^ 4 * H ^ 32 +
    (43097312460800 : K[X]) * a4 ^ 2 * a5 * a7 ^ 2 * H ^ 32 +
    (14656575897600 : K[X]) * a4 ^ 2 * a6 ^ 2 * a7 * H ^ 32 +
    (87939455385600 : K[X]) * a4 * a5 ^ 2 * a6 * a7 * H ^ 32 +
    (12213813248000 : K[X]) * a4 * a5 * a6 ^ 3 * H ^ 32 +
    (12213813248000 : K[X]) * a5 ^ 4 * a7 * H ^ 32 +
    (15877957222400 : K[X]) * a5 ^ 3 * a6 ^ 2 * H ^ 32 -
    (13679470837760 : K[X]) * a1 * b7 * a7 ^ 3 * H ^ 31 -
    (41038412513280 : K[X]) * a2 * b7 * a6 * a7 ^ 2 * H ^ 31 -
    (11725260718080 : K[X]) * a2 * b6 * a7 ^ 3 * H ^ 31 -
    (41038412513280 : K[X]) * a3 * a5 * b7 * a7 ^ 2 * H ^ 31 -
    (41038412513280 : K[X]) * a3 * b7 * a6 ^ 2 * a7 * H ^ 31 -
    (35175782154240 : K[X]) * a3 * b6 * a6 * a7 ^ 2 * H ^ 31 -
    (9771050598400 : K[X]) * a3 * b5 * a7 ^ 3 * H ^ 31 -
    (20519206256640 : K[X]) * a4 ^ 2 * b7 * a7 ^ 2 * H ^ 31 -
    (82076825026560 : K[X]) * a4 * a5 * b7 * a6 * a7 * H ^ 31 -
    (35175782154240 : K[X]) * a4 * a5 * b6 * a7 ^ 2 * H ^ 31 -
    (13679470837760 : K[X]) * a4 * b7 * a6 ^ 3 * H ^ 31 -
    (35175782154240 : K[X]) * a4 * b6 * a6 ^ 2 * a7 * H ^ 31 -
    (29313151795200 : K[X]) * a4 * b5 * a6 * a7 ^ 2 * H ^ 31 -
    (7816840478720 : K[X]) * a4 * b4 * a7 ^ 3 * H ^ 31 -
    (13679470837760 : K[X]) * a5 ^ 3 * b7 * a7 * H ^ 31 -
    (20519206256640 : K[X]) * a5 ^ 2 * b7 * a6 ^ 2 * H ^ 31 -
    (35175782154240 : K[X]) * a5 ^ 2 * b6 * a6 * a7 * H ^ 31 -
    (14656575897600 : K[X]) * a5 ^ 2 * b5 * a7 ^ 2 * H ^ 31 -
    (11725260718080 : K[X]) * a5 * b6 * a6 ^ 3 * H ^ 31 -
    (29313151795200 : K[X]) * a5 * b5 * a6 ^ 2 * a7 * H ^ 31 -
    (23450521436160 : K[X]) * a5 * b4 * a6 * a7 ^ 2 * H ^ 31 -
    (5862630359040 : K[X]) * a5 * b3 * a7 ^ 3 * H ^ 31 -
    (2442762649600 : K[X]) * b5 * a6 ^ 4 * H ^ 31 -
    (7816840478720 : K[X]) * b4 * a6 ^ 3 * a7 * H ^ 31 -
    (8793945538560 : K[X]) * b3 * a6 ^ 2 * a7 ^ 2 * H ^ 31 -
    (3908420239360 : K[X]) * b2 * a6 * a7 ^ 3 * H ^ 31 -
    (488552529920 : K[X]) * b1 * a7 ^ 4 * H ^ 31 +
    (1099243192320 : K[X]) * a0 * a7 ^ 5 * H ^ 28 +
    (8167987609600 : K[X]) * a1 * a6 * a7 ^ 4 * H ^ 28 -
    (9542041600000 : K[X]) * a2 * a5 * a7 ^ 4 * H ^ 28 +
    (19236755865600 : K[X]) * a2 * a6 ^ 2 * a7 ^ 3 * H ^ 28 -
    (9542041600000 : K[X]) * a3 * a4 * a7 ^ 4 * H ^ 28 -
    (32366605107200 : K[X]) * a3 * a5 * a6 * a7 ^ 3 * H ^ 28 +
    (19694773862400 : K[X]) * a3 * a6 ^ 3 * a7 ^ 2 * H ^ 28 -
    (16183302553600 : K[X]) * a4 ^ 2 * a6 * a7 ^ 3 * H ^ 28 -
    (51603360972800 : K[X]) * a4 * a5 ^ 2 * a7 ^ 3 * H ^ 28 -
    (47175853670400 : K[X]) * a4 * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 28 +
    (8855014604800 : K[X]) * a4 * a6 ^ 4 * a7 * H ^ 28 -
    (51145342976000 : K[X]) * a5 ^ 3 * a6 * a7 ^ 2 * H ^ 28 -
    (17710029209600 : K[X]) * a5 ^ 2 * a6 ^ 3 * a7 * H ^ 28 +
    (1328252190720 : K[X]) * a5 * a6 ^ 5 * H ^ 28 +
    (12397020446720 : K[X]) * a2 * b7 * a7 ^ 4 * H ^ 27 +
    (49588081786880 : K[X]) * a3 * b7 * a6 * a7 ^ 3 * H ^ 27 +
    (10626017525760 : K[X]) * a3 * b6 * a7 ^ 4 * H ^ 27 +
    (49588081786880 : K[X]) * a4 * a5 * b7 * a7 ^ 3 * H ^ 27 +
    (74382122680320 : K[X]) * a4 * b7 * a6 ^ 2 * a7 ^ 2 * H ^ 27 +
    (42504070103040 : K[X]) * a4 * b6 * a6 * a7 ^ 3 * H ^ 27 +
    (8855014604800 : K[X]) * a4 * b5 * a7 ^ 4 * H ^ 27 +
    (74382122680320 : K[X]) * a5 ^ 2 * b7 * a6 * a7 ^ 2 * H ^ 27 +
    (21252035051520 : K[X]) * a5 ^ 2 * b6 * a7 ^ 3 * H ^ 27 +
    (49588081786880 : K[X]) * a5 * b7 * a6 ^ 3 * a7 * H ^ 27 +
    (63756105154560 : K[X]) * a5 * b6 * a6 ^ 2 * a7 ^ 2 * H ^ 27 +
    (35420058419200 : K[X]) * a5 * b5 * a6 * a7 ^ 3 * H ^ 27 +
    (7084011683840 : K[X]) * a5 * b4 * a7 ^ 4 * H ^ 27 +
    (2479404089344 : K[X]) * b7 * a6 ^ 5 * H ^ 27 +
    (10626017525760 : K[X]) * b6 * a6 ^ 4 * a7 * H ^ 27 +
    (17710029209600 : K[X]) * b5 * a6 ^ 3 * a7 ^ 2 * H ^ 27 +
    (14168023367680 : K[X]) * b4 * a6 ^ 2 * a7 ^ 3 * H ^ 27 +
    (5313008762880 : K[X]) * b3 * a6 * a7 ^ 4 * H ^ 27 +
    (708401168384 : K[X]) * b2 * a7 ^ 5 * H ^ 27 -
    (857829539840 : K[X]) * a1 * a7 ^ 6 * H ^ 24 -
    (7526762414080 : K[X]) * a2 * a6 * a7 ^ 5 * H ^ 24 +
    (8855014604800 : K[X]) * a3 * a5 * a7 ^ 5 * H ^ 24 -
    (22552615321600 : K[X]) * a3 * a6 ^ 2 * a7 ^ 4 * H ^ 24 +
    (4427507302400 : K[X]) * a4 ^ 2 * a7 ^ 5 * H ^ 24 +
    (36803654451200 : K[X]) * a4 * a5 * a6 * a7 ^ 4 * H ^ 24 -
    (32099427942400 : K[X]) * a4 * a6 ^ 3 * a7 ^ 3 * H ^ 24 +
    (19785423257600 : K[X]) * a5 ^ 3 * a7 ^ 4 * H ^ 24 +
    (33759743180800 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 ^ 3 * H ^ 24 -
    (23382772940800 : K[X]) * a5 * a6 ^ 4 * a7 ^ 2 * H ^ 24 -
    (4095444254720 : K[X]) * a6 ^ 6 * a7 * H ^ 24 -
    (11467243913216 : K[X]) * a3 * b7 * a7 ^ 5 * H ^ 23 -
    (57336219566080 : K[X]) * a4 * b7 * a6 * a7 ^ 4 * H ^ 23 -
    (9829066211328 : K[X]) * a4 * b6 * a7 ^ 5 * H ^ 23 -
    (28668109783040 : K[X]) * a5 ^ 2 * b7 * a7 ^ 4 * H ^ 23 -
    (114672439132160 : K[X]) * a5 * b7 * a6 ^ 2 * a7 ^ 3 * H ^ 23 -
    (49145331056640 : K[X]) * a5 * b6 * a6 * a7 ^ 4 * H ^ 23 -
    (8190888509440 : K[X]) * a5 * b5 * a7 ^ 5 * H ^ 23 -
    (28668109783040 : K[X]) * b7 * a6 ^ 4 * a7 ^ 2 * H ^ 23 -
    (32763554037760 : K[X]) * b6 * a6 ^ 3 * a7 ^ 3 * H ^ 23 -
    (20477221273600 : K[X]) * b5 * a6 ^ 2 * a7 ^ 4 * H ^ 23 -
    (6552710807552 : K[X]) * b4 * a6 * a7 ^ 5 * H ^ 23 -
    (819088850944 : K[X]) * b3 * a7 ^ 6 * H ^ 23 +
    (694762864640 : K[X]) * a2 * a7 ^ 7 * H ^ 20 +
    (7039044812800 : K[X]) * a3 * a6 * a7 ^ 6 * H ^ 20 -
    (8318871142400 : K[X]) * a4 * a5 * a7 ^ 6 * H ^ 20 +
    (25596526592000 : K[X]) * a4 * a6 ^ 2 * a7 ^ 5 * H ^ 20 -
    (20477221273600 : K[X]) * a5 ^ 2 * a6 * a7 ^ 5 * H ^ 20 +
    (46713661030400 : K[X]) * a5 * a6 ^ 3 * a7 ^ 4 * H ^ 20 +
    (24828630794240 : K[X]) * a6 ^ 5 * a7 ^ 3 * H ^ 20 +
    (10750541168640 : K[X]) * a4 * b7 * a7 ^ 6 * H ^ 19 +
    (64503247011840 : K[X]) * a5 * b7 * a6 * a7 ^ 5 * H ^ 19 +
    (9214749573120 : K[X]) * a5 * b6 * a7 ^ 6 * H ^ 19 +
    (53752705843200 : K[X]) * b7 * a6 ^ 3 * a7 ^ 4 * H ^ 19 +
    (27644248719360 : K[X]) * b6 * a6 ^ 2 * a7 ^ 5 * H ^ 19 +
    (7678957977600 : K[X]) * b5 * a6 * a7 ^ 6 * H ^ 19 +
    (877595197440 : K[X]) * b4 * a7 ^ 7 * H ^ 19 -
    (578492928000 : K[X]) * a3 * a7 ^ 8 * H ^ 16 -
    (6650526105600 : K[X]) * a4 * a6 * a7 ^ 7 * H ^ 16 +
    (3942322176000 : K[X]) * a5 ^ 2 * a7 ^ 7 * H ^ 16 -
    (28436141260800 : K[X]) * a5 * a6 ^ 2 * a7 ^ 6 * H ^ 16 -
    (41274399129600 : K[X]) * a6 ^ 4 * a7 ^ 5 * H ^ 16 -
    (10174619320320 : K[X]) * a5 * b7 * a7 ^ 7 * H ^ 15 -
    (35611167621120 : K[X]) * b7 * a6 ^ 2 * a7 ^ 6 * H ^ 15 -
    (8721102274560 : K[X]) * b6 * a6 * a7 ^ 7 * H ^ 15 -
    (908448153600 : K[X]) * b5 * a7 ^ 8 * H ^ 15 +
    (492076083200 : K[X]) * a4 * a7 ^ 9 * H ^ 12 +
    (6330748070400 : K[X]) * a5 * a6 * a7 ^ 8 * H ^ 12 +
    (28843228876800 : K[X]) * a6 ^ 3 * a7 ^ 7 * H ^ 12 +
    (9697684039680 : K[X]) * b7 * a6 * a7 ^ 8 * H ^ 11 +
    (923588956160 : K[X]) * b6 * a7 ^ 9 * H ^ 11 -
    (425716784480 : K[X]) * a5 * a7 ^ 10 * H ^ 8 -
    (9668821884800 : K[X]) * a6 ^ 2 * a7 ^ 9 * H ^ 8 -
    (929361387136 : K[X]) * b7 * a7 ^ 10 * H ^ 7 +
    (1535105862680 : K[X]) * a6 * a7 ^ 11 * H ^ 4 -
    (92154224085 : K[X]) * a7 ^ 13 +
    Polynomial.C κ *
      (-(687194767360 : K[X]) * a0 * a5 * H ^ 43 -
        (687194767360 : K[X]) * a1 * a4 * H ^ 43 -
        (687194767360 : K[X]) * a2 * a3 * H ^ 43 +
        (1116691496960 : K[X]) * a0 * a6 * a7 * H ^ 39 +
        (1116691496960 : K[X]) * a1 * a5 * a7 * H ^ 39 +
        (558345748480 : K[X]) * a1 * a6 ^ 2 * H ^ 39 +
        (1116691496960 : K[X]) * a2 * a4 * a7 * H ^ 39 +
        (1116691496960 : K[X]) * a2 * a5 * a6 * H ^ 39 +
        (558345748480 : K[X]) * a3 ^ 2 * a7 * H ^ 39 +
        (1116691496960 : K[X]) * a3 * a4 * a6 * H ^ 39 +
        (558345748480 : K[X]) * a3 * a5 ^ 2 * H ^ 39 +
        (558345748480 : K[X]) * a4 ^ 2 * a5 * H ^ 39 -
        (488552529920 : K[X]) * a0 * a7 ^ 3 * H ^ 35 -
        (1465657589760 : K[X]) * a1 * a6 * a7 ^ 2 * H ^ 35 -
        (1465657589760 : K[X]) * a2 * a5 * a7 ^ 2 * H ^ 35 -
        (1465657589760 : K[X]) * a2 * a6 ^ 2 * a7 * H ^ 35 -
        (1465657589760 : K[X]) * a3 * a4 * a7 ^ 2 * H ^ 35 -
        (2931315179520 : K[X]) * a3 * a5 * a6 * a7 * H ^ 35 -
        (488552529920 : K[X]) * a3 * a6 ^ 3 * H ^ 35 -
        (1465657589760 : K[X]) * a4 ^ 2 * a6 * a7 * H ^ 35 -
        (1465657589760 : K[X]) * a4 * a5 ^ 2 * a7 * H ^ 35 -
        (1465657589760 : K[X]) * a4 * a5 * a6 ^ 2 * H ^ 35 -
        (488552529920 : K[X]) * a5 ^ 3 * a6 * H ^ 35 +
        (442750730240 : K[X]) * a1 * a7 ^ 4 * H ^ 31 +
        (1771002920960 : K[X]) * a2 * a6 * a7 ^ 3 * H ^ 31 +
        (1771002920960 : K[X]) * a3 * a5 * a7 ^ 3 * H ^ 31 +
        (2656504381440 : K[X]) * a3 * a6 ^ 2 * a7 ^ 2 * H ^ 31 +
        (885501460480 : K[X]) * a4 ^ 2 * a7 ^ 3 * H ^ 31 +
        (5313008762880 : K[X]) * a4 * a5 * a6 * a7 ^ 2 * H ^ 31 +
        (1771002920960 : K[X]) * a4 * a6 ^ 3 * a7 * H ^ 31 +
        (885501460480 : K[X]) * a5 ^ 3 * a7 ^ 2 * H ^ 31 +
        (2656504381440 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 * H ^ 31 +
        (442750730240 : K[X]) * a5 * a6 ^ 4 * H ^ 31 -
        (409544425472 : K[X]) * a2 * a7 ^ 5 * H ^ 27 -
        (2047722127360 : K[X]) * a3 * a6 * a7 ^ 4 * H ^ 27 -
        (2047722127360 : K[X]) * a4 * a5 * a7 ^ 4 * H ^ 27 -
        (4095444254720 : K[X]) * a4 * a6 ^ 2 * a7 ^ 3 * H ^ 27 -
        (4095444254720 : K[X]) * a5 ^ 2 * a6 * a7 ^ 3 * H ^ 27 -
        (4095444254720 : K[X]) * a5 * a6 ^ 3 * a7 ^ 2 * H ^ 27 -
        (409544425472 : K[X]) * a6 ^ 5 * a7 * H ^ 27 +
        (383947898880 : K[X]) * a3 * a7 ^ 6 * H ^ 23 +
        (2303687393280 : K[X]) * a4 * a6 * a7 ^ 5 * H ^ 23 +
        (1151843696640 : K[X]) * a5 ^ 2 * a7 ^ 5 * H ^ 23 +
        (5759218483200 : K[X]) * a5 * a6 ^ 2 * a7 ^ 4 * H ^ 23 +
        (1919739494400 : K[X]) * a6 ^ 4 * a7 ^ 3 * H ^ 23 -
        (363379261440 : K[X]) * a4 * a7 ^ 7 * H ^ 19 -
        (2543654830080 : K[X]) * a5 * a6 * a7 ^ 6 * H ^ 19 -
        (2543654830080 : K[X]) * a6 ^ 3 * a7 ^ 5 * H ^ 19 +
        (346345858560 : K[X]) * a5 * a7 ^ 8 * H ^ 15 +
        (1385383434240 : K[X]) * a6 ^ 2 * a7 ^ 7 * H ^ 15 -
        (331914781120 : K[X]) * a6 * a7 ^ 9 * H ^ 11 +
        (29042543348 : K[X]) * a7 ^ 11 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`4` Jacobian expression with the
weighted derivative of `N₁₃`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` through
degree-`5` rows.  The row sees only `q₀, …, q₅`, so no `N`- and no
`C`-correction occurs at all; for the first time three integral-tower
rows (`N₁₀`, `N₁₁` and `N₁₂`) correct simultaneously, and `q₀` couples
only through the `N₁₀`-row correction. -/
theorem alignedThirteenthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    (8796093022208 : K[X]) * H ^ 44 *
        (a4.derivative * b1 +
          a3.derivative * (b2 * (2 : K[X])) +
          a2.derivative * (b3 * (3 : K[X])) +
          a1.derivative * (b4 * (4 : K[X])) +
          a0.derivative * (b5 * (5 : K[X])) -
        ((a5 * (5 : K[X])) * b0.derivative +
          (a4 * (4 : K[X])) * b1.derivative +
          (a3 * (3 : K[X])) * b2.derivative +
          (a2 * (2 : K[X])) * b3.derivative +
          a1 * b4.derivative)) =
      ((2 : K[X]) * H *
          (alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ).derivative -
        (91 : K[X]) *
          alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ * H.derivative) +
        ((150323855360 : K[X]) * a0 * a6 * H ^ 32 +
            (150323855360 : K[X]) * a1 * a5 * H ^ 32 +
            (150323855360 : K[X]) * a2 * a4 * H ^ 32 +
            (75161927680 : K[X]) * a3 ^ 2 * H ^ 32 -
            (9395240960 : K[X]) * a0 * a7 ^ 2 * H ^ 28 -
            (18790481920 : K[X]) * a1 * a6 * a7 * H ^ 28 -
            (18790481920 : K[X]) * a2 * a5 * a7 * H ^ 28 -
            (9395240960 : K[X]) * a2 * a6 ^ 2 * H ^ 28 -
            (18790481920 : K[X]) * a3 * a4 * a7 * H ^ 28 -
            (18790481920 : K[X]) * a3 * a5 * a6 * H ^ 28 -
            (9395240960 : K[X]) * a4 ^ 2 * a6 * H ^ 28 -
            (9395240960 : K[X]) * a4 * a5 ^ 2 * H ^ 28 +
            (3523215360 : K[X]) * a1 * a7 ^ 3 * H ^ 24 +
            (10569646080 : K[X]) * a2 * a6 * a7 ^ 2 * H ^ 24 +
            (10569646080 : K[X]) * a3 * a5 * a7 ^ 2 * H ^ 24 +
            (10569646080 : K[X]) * a3 * a6 ^ 2 * a7 * H ^ 24 +
            (5284823040 : K[X]) * a4 ^ 2 * a7 ^ 2 * H ^ 24 +
            (21139292160 : K[X]) * a4 * a5 * a6 * a7 * H ^ 24 +
            (3523215360 : K[X]) * a4 * a6 ^ 3 * H ^ 24 +
            (3523215360 : K[X]) * a5 ^ 3 * a7 * H ^ 24 +
            (5284823040 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 24 -
            (1871708160 : K[X]) * a2 * a7 ^ 4 * H ^ 20 -
            (7486832640 : K[X]) * a3 * a6 * a7 ^ 3 * H ^ 20 -
            (7486832640 : K[X]) * a4 * a5 * a7 ^ 3 * H ^ 20 -
            (11230248960 : K[X]) * a4 * a6 ^ 2 * a7 ^ 2 * H ^ 20 -
            (11230248960 : K[X]) * a5 ^ 2 * a6 * a7 ^ 2 * H ^ 20 -
            (7486832640 : K[X]) * a5 * a6 ^ 3 * a7 * H ^ 20 -
            (374341632 : K[X]) * a6 ^ 5 * H ^ 20 +
            (1169817600 : K[X]) * a3 * a7 ^ 5 * H ^ 16 +
            (5849088000 : K[X]) * a4 * a6 * a7 ^ 4 * H ^ 16 +
            (2924544000 : K[X]) * a5 ^ 2 * a7 ^ 4 * H ^ 16 +
            (11698176000 : K[X]) * a5 * a6 ^ 2 * a7 ^ 3 * H ^ 16 +
            (2924544000 : K[X]) * a6 ^ 4 * a7 ^ 2 * H ^ 16 -
            (804249600 : K[X]) * a4 * a7 ^ 6 * H ^ 12 -
            (4825497600 : K[X]) * a5 * a6 * a7 ^ 5 * H ^ 12 -
            (4021248000 : K[X]) * a6 ^ 3 * a7 ^ 4 * H ^ 12 +
            (588825600 : K[X]) * a5 * a7 ^ 7 * H ^ 8 +
            (2060889600 : K[X]) * a6 ^ 2 * a7 ^ 6 * H ^ 8 -
            (450819600 : K[X]) * a6 * a7 ^ 8 * H ^ 4 +
            (35689885 : K[X]) * a7 ^ 10) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((16106127360 : K[X]) * a0 * a7 * H ^ 28 +
            (16106127360 : K[X]) * a1 * a6 * H ^ 28 +
            (16106127360 : K[X]) * a2 * a5 * H ^ 28 +
            (16106127360 : K[X]) * a3 * a4 * H ^ 28 -
            (2013265920 : K[X]) * a1 * a7 ^ 2 * H ^ 24 -
            (4026531840 : K[X]) * a2 * a6 * a7 * H ^ 24 -
            (4026531840 : K[X]) * a3 * a5 * a7 * H ^ 24 -
            (2013265920 : K[X]) * a3 * a6 ^ 2 * H ^ 24 -
            (2013265920 : K[X]) * a4 ^ 2 * a7 * H ^ 24 -
            (4026531840 : K[X]) * a4 * a5 * a6 * H ^ 24 -
            (671088640 : K[X]) * a5 ^ 3 * H ^ 24 +
            (838860800 : K[X]) * a2 * a7 ^ 3 * H ^ 20 +
            (2516582400 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 20 +
            (2516582400 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 20 +
            (2516582400 : K[X]) * a4 * a6 ^ 2 * a7 * H ^ 20 +
            (2516582400 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 20 +
            (838860800 : K[X]) * a5 * a6 ^ 3 * H ^ 20 -
            (471859200 : K[X]) * a3 * a7 ^ 4 * H ^ 16 -
            (1887436800 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 16 -
            (943718400 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 16 -
            (2831155200 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 16 -
            (471859200 : K[X]) * a6 ^ 4 * a7 * H ^ 16 +
            (306708480 : K[X]) * a4 * a7 ^ 5 * H ^ 12 +
            (1533542400 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 12 +
            (1022361600 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 12 -
            (217251840 : K[X]) * a5 * a7 ^ 6 * H ^ 8 -
            (651755520 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 8 +
            (162938880 : K[X]) * a6 * a7 ^ 7 * H ^ 4 -
            (14144000 : K[X]) * a7 ^ 9) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((1342177280 : K[X]) * a0 * H ^ 28 +
            (838860800 : K[X]) * a1 * a7 * H ^ 24 +
            (838860800 : K[X]) * a2 * a6 * H ^ 24 +
            (838860800 : K[X]) * a3 * a5 * H ^ 24 +
            (419430400 : K[X]) * a4 ^ 2 * H ^ 24 -
            (157286400 : K[X]) * a2 * a7 ^ 2 * H ^ 20 -
            (314572800 : K[X]) * a3 * a6 * a7 * H ^ 20 -
            (314572800 : K[X]) * a4 * a5 * a7 * H ^ 20 -
            (157286400 : K[X]) * a4 * a6 ^ 2 * H ^ 20 -
            (157286400 : K[X]) * a5 ^ 2 * a6 * H ^ 20 +
            (72089600 : K[X]) * a3 * a7 ^ 3 * H ^ 16 +
            (216268800 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 16 +
            (108134400 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 16 +
            (216268800 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 16 +
            (18022400 : K[X]) * a6 ^ 4 * H ^ 16 -
            (42803200 : K[X]) * a4 * a7 ^ 4 * H ^ 12 -
            (171212800 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 12 -
            (85606400 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 12 +
            (28892160 : K[X]) * a5 * a7 ^ 5 * H ^ 8 +
            (72230400 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 8 -
            (21067200 : K[X]) * a6 * a7 ^ 6 * H ^ 4 +
            (2022075 : K[X]) * a7 ^ 8) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((671088640 : K[X]) * a1 * H ^ 24 +
            (335544320 : K[X]) * a2 * a7 * H ^ 20 +
            (335544320 : K[X]) * a3 * a6 * H ^ 20 +
            (335544320 : K[X]) * a4 * a5 * H ^ 20 -
            (83886080 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
            (167772160 : K[X]) * a4 * a6 * a7 * H ^ 16 -
            (83886080 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
            (83886080 : K[X]) * a5 * a6 ^ 2 * H ^ 16 +
            (41943040 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
            (125829120 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
            (41943040 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
            (26214400 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
            (52428800 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
            (18350080 : K[X]) * a6 * a7 ^ 5 * H ^ 4 -
            (1966080 : K[X]) * a7 ^ 7) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((5242880 : K[X]) * a2 * H ^ 20 +
            (1966080 : K[X]) * a3 * a7 * H ^ 16 +
            (1966080 : K[X]) * a4 * a6 * H ^ 16 +
            (983040 : K[X]) * a5 ^ 2 * H ^ 16 -
            (614400 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (1228800 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (204800 : K[X]) * a6 ^ 3 * H ^ 12 +
            (332800 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (499200 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (218400 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (26390 : K[X]) * a7 ^ 6) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        ((1310720 : K[X]) * a3 * H ^ 16 +
            (327680 : K[X]) * a4 * a7 * H ^ 12 +
            (327680 : K[X]) * a5 * a6 * H ^ 12 -
            (122880 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (122880 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (71680 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (9856 : K[X]) * a7 ^ 5) *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        ((40960 : K[X]) * a4 * H ^ 12 +
            (5120 : K[X]) * a5 * a7 * H ^ 8 +
            (2560 : K[X]) * a6 ^ 2 * H ^ 8 -
            (2240 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (350 : K[X]) * a7 ^ 4) *
          ((2 : K[X]) * H *
              (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ).derivative -
            (63 : K[X]) *
              alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        (40960 : K[X]) * a5 * H ^ 8 *
          (H * (alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (35 : K[X]) *
              alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        ((80 : K[X]) * a6 * H ^ 4 - (5 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (77 : K[X]) *
              alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) +
        (20 : K[X]) * a7 *
          (H * (alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (42 : K[X]) *
              alignedTwelfthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedThirteenthDefect810, alignedTwelfthDefect810,
    alignedEleventhDefect810, alignedTenthDefect810, alignedNinthDefect810,
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
degree-`5` rows, the degree-`4` row is the weighted derivative
`2 H N₁₃' - 91 N₁₃ H' = 0`. -/
theorem alignedThirteenthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (91 : K[X]) *
        alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedThirteenthCoefficientJacobianRow_810 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5] at hrow
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
  have hid := alignedThirteenthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 0) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) κ
  rw [hrow, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ, hrowL, hrowN,
    hrowN11, hrowN12] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

set_option maxHeartbeats 8000000 in
/-- Squared weight-ninety-one polynomial first integral of the aligned
`(8,10)` thirteenth defect: `N₁₃² = κ₁₂ H⁹¹`.  The exponent is odd, so
the integral is chambered. -/
theorem alignedThirteenthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₁₂ : K,
      alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₁₂ * H ^ 91 := by
  let N : K[X] :=
    alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * N.derivative -
        (91 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      alignedThirteenthDefectRow_eq_zero_810 hp hq hjac hp8 hq10
        haligned hM
  have hC91 : Polynomial.C (91 : K) = (91 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (N ^ 2) (H ^ 91) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      N ^ 2 * (Polynomial.C (91 : K) * H ^ (91 - 1) * H.derivative) -
          Polynomial.C (2 : K) * N ^ (2 - 1) * N.derivative * H ^ 91 =
          N * H ^ 90 *
            (Polynomial.C (91 : K) * N * H.derivative -
              Polynomial.C (2 : K) * H * N.derivative) := by
        ring
      _ = 0 := by
        rw [hC91, hC2]
        have hfac :
            (91 : K[X]) * N * H.derivative -
              (2 : K[X]) * H * N.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 91 hH) hW

/-! ## Root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport thirteenth row at a root of its
co-factor: either the descent quotient vanishes there, or the even
dodecic core `19258981 g¹² - 298574016 p₆ g¹⁰ + 1809391168 p₆² g⁸
- 5384491008 p₆³ g⁶ + 8054079488 p₆⁴ g⁴ - 5438963712 p₆⁵ g²
+ 1145044992 p₆⁶` does.  Neither branch is excluded. -/
theorem alignedThirteenth_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (2900 : K[X]) * g *
        ((19258981 : K[X]) * g ^ 12 - (298574016 : K[X]) * a6 * g ^ 10 +
          (1809391168 : K[X]) * a6 ^ 2 * g ^ 8 -
          (5384491008 : K[X]) * a6 ^ 3 * g ^ 6 +
          (8054079488 : K[X]) * a6 ^ 4 * g ^ 4 -
          (5438963712 : K[X]) * a6 ^ 5 * g ^ 2 +
          (1145044992 : K[X]) * a6 ^ 6) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨
      19258981 * (g.eval a) ^ 12 - 298574016 * a6.eval a * (g.eval a) ^ 10 +
        1809391168 * (a6.eval a) ^ 2 * (g.eval a) ^ 8 -
        5384491008 * (a6.eval a) ^ 3 * (g.eval a) ^ 6 +
        8054079488 * (a6.eval a) ^ 4 * (g.eval a) ^ 4 -
        5438963712 * (a6.eval a) ^ 5 * (g.eval a) ^ 2 +
        1145044992 * (a6.eval a) ^ 6 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h2900g | hdodecic
  · exact Or.inl
      ((mul_eq_zero.mp h2900g).resolve_left
        (by norm_num : (2900 : K) ≠ 0))
  · exact Or.inr (by linear_combination hdodecic)

/-- The root tridecic of the consumed degree-`4` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the thirteenth row adds no new root
constraint. -/
theorem alignedThirteenth_rootTridecic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    2900 * G * (19258981 * G ^ 12 - 298574016 * P6 * G ^ 10 +
      1809391168 * P6 ^ 2 * G ^ 8 - 5384491008 * P6 ^ 3 * G ^ 6 +
      8054079488 * P6 ^ 4 * G ^ 4 - 5438963712 * P6 ^ 5 * G ^ 2 +
      1145044992 * P6 ^ 6) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared thirteenth rows and transport co-factors -/

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the square-chamber thirteenth row
(`H = h₀²`, `p₇ = h₀⁴ g₁`, `h₀⁵²` peeled, `128 q₇ h₀²` consumed): the
`q₁` head is `4398046511104 p₄ q₁ h₀³⁰`, i.e. `q₁, …, q₆` are re-tied
at the weight-thirty-five level here and at weight thirty-nine in the
cleared row. -/
def alignedThirteenthSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
    -(27487790694400 : K[X]) * a0 * a3 * h0 ^ 32 -
    (27487790694400 : K[X]) * a1 * a2 * h0 ^ 32 +
    (21990232555520 : K[X]) * a0 * b5 * h0 ^ 30 +
    (17592186044416 : K[X]) * a1 * b4 * h0 ^ 30 +
    (13194139533312 : K[X]) * a2 * b3 * h0 ^ 30 +
    (8796093022208 : K[X]) * a3 * b2 * h0 ^ 30 +
    (4398046511104 : K[X]) * a4 * b1 * h0 ^ 30 +
    (13743895347200 : K[X]) * a0 * a4 * g1 * h0 ^ 28 +
    (13743895347200 : K[X]) * a1 * a3 * g1 * h0 ^ 28 +
    (6871947673600 : K[X]) * a2 ^ 2 * g1 * h0 ^ 28 -
    (16492674416640 : K[X]) * a0 * b6 * g1 * h0 ^ 26 -
    (13743895347200 : K[X]) * a1 * b5 * g1 * h0 ^ 26 -
    (10995116277760 : K[X]) * a2 * b4 * g1 * h0 ^ 26 -
    (8246337208320 : K[X]) * a3 * b3 * g1 * h0 ^ 26 -
    (5497558138880 : K[X]) * a4 * b2 * g1 * h0 ^ 26 -
    (2748779069440 : K[X]) * a5 * b1 * g1 * h0 ^ 26 -
    (6871947673600 : K[X]) * a0 * a5 * a6 * h0 ^ 24 +
    (7730941132800 : K[X]) * a0 * a5 * g1 ^ 2 * h0 ^ 24 +
    (17179869184000 : K[X]) * a1 * a4 * a6 * h0 ^ 24 -
    (11811160064000 : K[X]) * a1 * a4 * g1 ^ 2 * h0 ^ 24 -
    (1717986918400 : K[X]) * a1 * a5 ^ 2 * h0 ^ 24 +
    (17179869184000 : K[X]) * a2 * a3 * a6 * h0 ^ 24 -
    (11811160064000 : K[X]) * a2 * a3 * g1 ^ 2 * h0 ^ 24 +
    (20615843020800 : K[X]) * a2 * a4 * a5 * h0 ^ 24 +
    (10307921510400 : K[X]) * a3 ^ 2 * a5 * h0 ^ 24 +
    (22333829939200 : K[X]) * a3 * a4 ^ 2 * h0 ^ 24 -
    (16492674416640 : K[X]) * a1 * b6 * a6 * h0 ^ 22 +
    (13400297963520 : K[X]) * a1 * b6 * g1 ^ 2 * h0 ^ 22 -
    (16492674416640 : K[X]) * a2 * a5 * b6 * h0 ^ 22 -
    (13743895347200 : K[X]) * a2 * b5 * a6 * h0 ^ 22 +
    (11166914969600 : K[X]) * a2 * b5 * g1 ^ 2 * h0 ^ 22 -
    (16492674416640 : K[X]) * a3 * a4 * b6 * h0 ^ 22 -
    (13743895347200 : K[X]) * a3 * a5 * b5 * h0 ^ 22 -
    (10995116277760 : K[X]) * a3 * b4 * a6 * h0 ^ 22 +
    (8933531975680 : K[X]) * a3 * b4 * g1 ^ 2 * h0 ^ 22 -
    (6871947673600 : K[X]) * a4 ^ 2 * b5 * h0 ^ 22 -
    (10995116277760 : K[X]) * a4 * a5 * b4 * h0 ^ 22 -
    (8246337208320 : K[X]) * a4 * b3 * a6 * h0 ^ 22 +
    (6700148981760 : K[X]) * a4 * b3 * g1 ^ 2 * h0 ^ 22 -
    (4123168604160 : K[X]) * a5 ^ 2 * b3 * h0 ^ 22 -
    (5497558138880 : K[X]) * a5 * b2 * a6 * h0 ^ 22 +
    (4466765987840 : K[X]) * a5 * b2 * g1 ^ 2 * h0 ^ 22 -
    (1374389534720 : K[X]) * b1 * a6 ^ 2 * h0 ^ 22 +
    (2233382993920 : K[X]) * b1 * a6 * g1 ^ 2 * h0 ^ 22 -
    (488552529920 : K[X]) * b1 * g1 ^ 4 * h0 ^ 22 +
    (5153960755200 : K[X]) * a0 * a6 ^ 2 * g1 * h0 ^ 20 -
    (3435973836800 : K[X]) * a0 * a6 * g1 ^ 3 * h0 ^ 20 +
    (488552529920 : K[X]) * a0 * g1 ^ 5 * h0 ^ 20 +
    (10737418240000 : K[X]) * a1 * a5 * a6 * g1 * h0 ^ 20 -
    (5878736486400 : K[X]) * a1 * a5 * g1 ^ 3 * h0 ^ 20 -
    (28346784153600 : K[X]) * a2 * a4 * a6 * g1 * h0 ^ 20 +
    (11220602060800 : K[X]) * a2 * a4 * g1 ^ 3 * h0 ^ 20 +
    (5583457484800 : K[X]) * a2 * a5 ^ 2 * g1 * h0 ^ 20 -
    (14173392076800 : K[X]) * a3 ^ 2 * a6 * g1 * h0 ^ 20 +
    (5610301030400 : K[X]) * a3 ^ 2 * g1 ^ 3 * h0 ^ 20 -
    (27917287424000 : K[X]) * a3 * a4 * a5 * g1 * h0 ^ 20 -
    (11166914969600 : K[X]) * a4 ^ 3 * g1 * h0 ^ 20 +
    (26800595927040 : K[X]) * a2 * b6 * a6 * g1 * h0 ^ 18 -
    (11725260718080 : K[X]) * a2 * b6 * g1 ^ 3 * h0 ^ 18 +
    (26800595927040 : K[X]) * a3 * a5 * b6 * g1 * h0 ^ 18 +
    (22333829939200 : K[X]) * a3 * b5 * a6 * g1 * h0 ^ 18 -
    (9771050598400 : K[X]) * a3 * b5 * g1 ^ 3 * h0 ^ 18 +
    (13400297963520 : K[X]) * a4 ^ 2 * b6 * g1 * h0 ^ 18 +
    (22333829939200 : K[X]) * a4 * a5 * b5 * g1 * h0 ^ 18 +
    (17867063951360 : K[X]) * a4 * b4 * a6 * g1 * h0 ^ 18 -
    (7816840478720 : K[X]) * a4 * b4 * g1 ^ 3 * h0 ^ 18 +
    (8933531975680 : K[X]) * a5 ^ 2 * b4 * g1 * h0 ^ 18 +
    (13400297963520 : K[X]) * a5 * b3 * a6 * g1 * h0 ^ 18 -
    (5862630359040 : K[X]) * a5 * b3 * g1 ^ 3 * h0 ^ 18 +
    (4466765987840 : K[X]) * b2 * a6 ^ 2 * g1 * h0 ^ 18 -
    (3908420239360 : K[X]) * b2 * a6 * g1 ^ 3 * h0 ^ 18 +
    (708401168384 : K[X]) * b2 * g1 ^ 5 * h0 ^ 18 +
    (2791728742400 : K[X]) * a1 * a6 ^ 3 * h0 ^ 16 -
    (5757940531200 : K[X]) * a1 * a6 ^ 2 * g1 ^ 2 * h0 ^ 16 +
    (2671771648000 : K[X]) * a1 * a6 * g1 ^ 4 * h0 ^ 16 -
    (323475210240 : K[X]) * a1 * g1 ^ 6 * h0 ^ 16 +
    (5583457484800 : K[X]) * a2 * a5 * a6 ^ 2 * h0 ^ 16 -
    (13958643712000 : K[X]) * a2 * a5 * a6 * g1 ^ 2 * h0 ^ 16 +
    (4732852633600 : K[X]) * a2 * a5 * g1 ^ 4 * h0 ^ 16 -
    (13958643712000 : K[X]) * a3 * a4 * a6 ^ 2 * h0 ^ 16 +
    (37339371929600 : K[X]) * a3 * a4 * a6 * g1 ^ 2 * h0 ^ 16 -
    (10763422924800 : K[X]) * a3 * a4 * g1 ^ 4 * h0 ^ 16 +
    (2791728742400 : K[X]) * a3 * a5 ^ 2 * a6 * h0 ^ 16 -
    (8200703180800 : K[X]) * a3 * a5 ^ 2 * g1 ^ 2 * h0 ^ 16 -
    (16750372454400 : K[X]) * a4 ^ 2 * a5 * a6 * h0 ^ 16 +
    (17448304640000 : K[X]) * a4 ^ 2 * a5 * g1 ^ 2 * h0 ^ 16 +
    (13400297963520 : K[X]) * a3 * b6 * a6 ^ 2 * h0 ^ 14 -
    (35175782154240 : K[X]) * a3 * b6 * a6 * g1 ^ 2 * h0 ^ 14 +
    (10626017525760 : K[X]) * a3 * b6 * g1 ^ 4 * h0 ^ 14 +
    (26800595927040 : K[X]) * a4 * a5 * b6 * a6 * h0 ^ 14 -
    (35175782154240 : K[X]) * a4 * a5 * b6 * g1 ^ 2 * h0 ^ 14 +
    (11166914969600 : K[X]) * a4 * b5 * a6 ^ 2 * h0 ^ 14 -
    (29313151795200 : K[X]) * a4 * b5 * a6 * g1 ^ 2 * h0 ^ 14 +
    (8855014604800 : K[X]) * a4 * b5 * g1 ^ 4 * h0 ^ 14 +
    (4466765987840 : K[X]) * a5 ^ 3 * b6 * h0 ^ 14 +
    (11166914969600 : K[X]) * a5 ^ 2 * b5 * a6 * h0 ^ 14 -
    (14656575897600 : K[X]) * a5 ^ 2 * b5 * g1 ^ 2 * h0 ^ 14 +
    (8933531975680 : K[X]) * a5 * b4 * a6 ^ 2 * h0 ^ 14 -
    (23450521436160 : K[X]) * a5 * b4 * a6 * g1 ^ 2 * h0 ^ 14 +
    (7084011683840 : K[X]) * a5 * b4 * g1 ^ 4 * h0 ^ 14 +
    (2233382993920 : K[X]) * b3 * a6 ^ 3 * h0 ^ 14 -
    (8793945538560 : K[X]) * b3 * a6 ^ 2 * g1 ^ 2 * h0 ^ 14 +
    (5313008762880 : K[X]) * b3 * a6 * g1 ^ 4 * h0 ^ 14 -
    (819088850944 : K[X]) * b3 * g1 ^ 6 * h0 ^ 14 -
    (4885525299200 : K[X]) * a2 * a6 ^ 3 * g1 * h0 ^ 12 +
    (5801561292800 : K[X]) * a2 * a6 ^ 2 * g1 ^ 3 * h0 ^ 12 -
    (2049630535680 : K[X]) * a2 * a6 * g1 ^ 5 * h0 ^ 12 +
    (210504253440 : K[X]) * a2 * g1 ^ 7 * h0 ^ 12 -
    (12213813248000 : K[X]) * a3 * a5 * a6 ^ 2 * g1 * h0 ^ 12 +
    (15572611891200 : K[X]) * a3 * a5 * a6 * g1 ^ 3 * h0 ^ 12 -
    (3875977297920 : K[X]) * a3 * a5 * g1 ^ 5 * h0 ^ 12 +
    (19542101196800 : K[X]) * a4 ^ 2 * a6 ^ 2 * g1 * h0 ^ 12 -
    (23206245171200 : K[X]) * a4 ^ 2 * a6 * g1 ^ 3 * h0 ^ 12 +
    (5229038796800 : K[X]) * a4 ^ 2 * g1 ^ 5 * h0 ^ 12 -
    (9771050598400 : K[X]) * a4 * a5 ^ 2 * a6 * g1 * h0 ^ 12 +
    (9771050598400 : K[X]) * a4 * a5 ^ 2 * g1 ^ 3 * h0 ^ 12 -
    (4885525299200 : K[X]) * a5 ^ 4 * g1 * h0 ^ 12 -
    (35175782154240 : K[X]) * a4 * b6 * a6 ^ 2 * g1 * h0 ^ 10 +
    (42504070103040 : K[X]) * a4 * b6 * a6 * g1 ^ 3 * h0 ^ 10 -
    (9829066211328 : K[X]) * a4 * b6 * g1 ^ 5 * h0 ^ 10 -
    (35175782154240 : K[X]) * a5 ^ 2 * b6 * a6 * g1 * h0 ^ 10 +
    (21252035051520 : K[X]) * a5 ^ 2 * b6 * g1 ^ 3 * h0 ^ 10 -
    (29313151795200 : K[X]) * a5 * b5 * a6 ^ 2 * g1 * h0 ^ 10 +
    (35420058419200 : K[X]) * a5 * b5 * a6 * g1 ^ 3 * h0 ^ 10 -
    (8190888509440 : K[X]) * a5 * b5 * g1 ^ 5 * h0 ^ 10 -
    (7816840478720 : K[X]) * b4 * a6 ^ 3 * g1 * h0 ^ 10 +
    (14168023367680 : K[X]) * b4 * a6 ^ 2 * g1 ^ 3 * h0 ^ 10 -
    (6552710807552 : K[X]) * b4 * a6 * g1 ^ 5 * h0 ^ 10 +
    (877595197440 : K[X]) * b4 * g1 ^ 7 * h0 ^ 10 -
    (1832071987200 : K[X]) * a3 * a6 ^ 4 * h0 ^ 8 +
    (6870269952000 : K[X]) * a3 * a6 ^ 3 * g1 ^ 2 * h0 ^ 8 -
    (5453276774400 : K[X]) * a3 * a6 ^ 2 * g1 ^ 4 * h0 ^ 8 +
    (1518496645120 : K[X]) * a3 * a6 * g1 ^ 6 * h0 ^ 8 -
    (130553712640 : K[X]) * a3 * g1 ^ 8 * h0 ^ 8 -
    (4885525299200 : K[X]) * a4 * a5 * a6 ^ 3 * h0 ^ 8 +
    (20152791859200 : K[X]) * a4 * a5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 8 -
    (16164218470400 : K[X]) * a4 * a5 * a6 * g1 ^ 4 * h0 ^ 8 +
    (3182270873600 : K[X]) * a4 * a5 * g1 ^ 6 * h0 ^ 8 -
    (9771050598400 : K[X]) * a5 ^ 3 * a6 ^ 2 * h0 ^ 8 +
    (37557475737600 : K[X]) * a5 ^ 3 * a6 * g1 ^ 2 * h0 ^ 8 -
    (15515359641600 : K[X]) * a5 ^ 3 * g1 ^ 4 * h0 ^ 8 -
    (11725260718080 : K[X]) * a5 * b6 * a6 ^ 3 * h0 ^ 6 +
    (63756105154560 : K[X]) * a5 * b6 * a6 ^ 2 * g1 ^ 2 * h0 ^ 6 -
    (49145331056640 : K[X]) * a5 * b6 * a6 * g1 ^ 4 * h0 ^ 6 +
    (9214749573120 : K[X]) * a5 * b6 * g1 ^ 6 * h0 ^ 6 -
    (2442762649600 : K[X]) * b5 * a6 ^ 4 * h0 ^ 6 +
    (17710029209600 : K[X]) * b5 * a6 ^ 3 * g1 ^ 2 * h0 ^ 6 -
    (20477221273600 : K[X]) * b5 * a6 ^ 2 * g1 ^ 4 * h0 ^ 6 +
    (7678957977600 : K[X]) * b5 * a6 * g1 ^ 6 * h0 ^ 6 -
    (908448153600 : K[X]) * b5 * g1 ^ 8 * h0 ^ 6 +
    (4580179968000 : K[X]) * a4 * a6 ^ 4 * g1 * h0 ^ 4 -
    (8320660275200 : K[X]) * a4 * a6 ^ 3 * g1 ^ 3 * h0 ^ 4 +
    (4773406310400 : K[X]) * a4 * a6 ^ 2 * g1 ^ 5 * h0 ^ 4 -
    (1051285913600 : K[X]) * a4 * a6 * g1 ^ 7 * h0 ^ 4 +
    (72133068800 : K[X]) * a4 * g1 ^ 9 * h0 ^ 4 +
    (37862821068800 : K[X]) * a5 ^ 2 * a6 ^ 3 * g1 * h0 ^ 4 -
    (85534860902400 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 ^ 3 * h0 ^ 4 +
    (48287501516800 : K[X]) * a5 ^ 2 * a6 * g1 ^ 5 * h0 ^ 4 -
    (7656103936000 : K[X]) * a5 ^ 2 * g1 ^ 7 * h0 ^ 4 +
    (10626017525760 : K[X]) * b6 * a6 ^ 4 * g1 * h0 ^ 2 -
    (32763554037760 : K[X]) * b6 * a6 ^ 3 * g1 ^ 3 * h0 ^ 2 +
    (27644248719360 : K[X]) * b6 * a6 ^ 2 * g1 ^ 5 * h0 ^ 2 -
    (8721102274560 : K[X]) * b6 * a6 * g1 ^ 7 * h0 ^ 2 +
    (923588956160 : K[X]) * b6 * g1 ^ 9 * h0 ^ 2 +
    (4427507302400 : K[X]) * a5 * a6 ^ 5 -
    (43721634611200 : K[X]) * a5 * a6 ^ 4 * g1 ^ 2 +
    (76132371660800 : K[X]) * a5 * a6 ^ 3 * g1 ^ 4 -
    (48313443942400 : K[X]) * a5 * a6 ^ 2 * g1 ^ 6 +
    (12753626496000 : K[X]) * a5 * a6 * g1 ^ 8 -
    (1189972451200 : K[X]) * a5 * g1 ^ 10 +
    Polynomial.C κ *
      (-(687194767360 : K[X]) * a0 * a5 * h0 ^ 30 -
        (687194767360 : K[X]) * a1 * a4 * h0 ^ 30 -
        (687194767360 : K[X]) * a2 * a3 * h0 ^ 30 +
        (515396075520 : K[X]) * a0 * a6 * g1 * h0 ^ 26 +
        (515396075520 : K[X]) * a1 * a5 * g1 * h0 ^ 26 +
        (515396075520 : K[X]) * a2 * a4 * g1 * h0 ^ 26 +
        (257698037760 : K[X]) * a3 ^ 2 * g1 * h0 ^ 26 +
        (558345748480 : K[X]) * a1 * a6 ^ 2 * h0 ^ 22 -
        (488552529920 : K[X]) * a1 * a6 * g1 ^ 2 * h0 ^ 22 +
        (15267266560 : K[X]) * a1 * g1 ^ 4 * h0 ^ 22 +
        (1116691496960 : K[X]) * a2 * a5 * a6 * h0 ^ 22 -
        (488552529920 : K[X]) * a2 * a5 * g1 ^ 2 * h0 ^ 22 +
        (1116691496960 : K[X]) * a3 * a4 * a6 * h0 ^ 22 -
        (488552529920 : K[X]) * a3 * a4 * g1 ^ 2 * h0 ^ 22 +
        (558345748480 : K[X]) * a3 * a5 ^ 2 * h0 ^ 22 +
        (558345748480 : K[X]) * a4 ^ 2 * a5 * h0 ^ 22 -
        (977105059840 : K[X]) * a2 * a6 ^ 2 * g1 * h0 ^ 18 +
        (488552529920 : K[X]) * a2 * a6 * g1 ^ 3 * h0 ^ 18 -
        (22137536512 : K[X]) * a2 * g1 ^ 5 * h0 ^ 18 -
        (1954210119680 : K[X]) * a3 * a5 * a6 * g1 * h0 ^ 18 +
        (488552529920 : K[X]) * a3 * a5 * g1 ^ 3 * h0 ^ 18 -
        (977105059840 : K[X]) * a4 ^ 2 * a6 * g1 * h0 ^ 18 +
        (244276264960 : K[X]) * a4 ^ 2 * g1 ^ 3 * h0 ^ 18 -
        (977105059840 : K[X]) * a4 * a5 ^ 2 * g1 * h0 ^ 18 -
        (488552529920 : K[X]) * a3 * a6 ^ 3 * h0 ^ 14 +
        (1374053990400 : K[X]) * a3 * a6 ^ 2 * g1 ^ 2 * h0 ^ 14 -
        (498094571520 : K[X]) * a3 * a6 * g1 ^ 4 * h0 ^ 14 +
        (25596526592 : K[X]) * a3 * g1 ^ 6 * h0 ^ 14 -
        (1465657589760 : K[X]) * a4 * a5 * a6 ^ 2 * h0 ^ 14 +
        (2748107980800 : K[X]) * a4 * a5 * a6 * g1 ^ 2 * h0 ^ 14 -
        (498094571520 : K[X]) * a4 * a5 * g1 ^ 4 * h0 ^ 14 -
        (488552529920 : K[X]) * a5 ^ 3 * a6 * h0 ^ 14 +
        (458017996800 : K[X]) * a5 ^ 3 * g1 ^ 2 * h0 ^ 14 +
        (1343519457280 : K[X]) * a4 * a6 ^ 3 * g1 * h0 ^ 10 -
        (1771002920960 : K[X]) * a4 * a6 ^ 2 * g1 ^ 3 * h0 ^ 10 +
        (511930531840 : K[X]) * a4 * a6 * g1 ^ 5 * h0 ^ 10 -
        (27424849920 : K[X]) * a4 * g1 ^ 7 * h0 ^ 10 +
        (2015279185920 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 * h0 ^ 10 -
        (1771002920960 : K[X]) * a5 ^ 2 * a6 * g1 ^ 3 * h0 ^ 10 +
        (255965265920 : K[X]) * a5 ^ 2 * g1 ^ 5 * h0 ^ 10 +
        (442750730240 : K[X]) * a5 * a6 ^ 4 * h0 ^ 6 -
        (2545816698880 : K[X]) * a5 * a6 ^ 3 * g1 ^ 2 * h0 ^ 6 +
        (2175704760320 : K[X]) * a5 * a6 ^ 2 * g1 ^ 4 * h0 ^ 6 -
        (527928360960 : K[X]) * a5 * a6 * g1 ^ 6 * h0 ^ 6 +
        (28389004800 : K[X]) * a5 * g1 ^ 8 * h0 ^ 6 -
        (332063047680 : K[X]) * a6 ^ 5 * g1 * h0 ^ 2 +
        (1023861063680 : K[X]) * a6 ^ 4 * g1 ^ 3 * h0 ^ 2 -
        (863882772480 : K[X]) * a6 ^ 3 * g1 ^ 5 * h0 ^ 2 +
        (272534446080 : K[X]) * a6 ^ 2 * g1 ^ 7 * h0 ^ 2 -
        (28862154880 : K[X]) * a6 * g1 ^ 9 * h0 ^ 2) -
    Polynomial.C μ *
      (-(150323855360 : K[X]) * a0 * a6 * h0 ^ 29 +
        (122138132480 : K[X]) * a0 * g1 ^ 2 * h0 ^ 29 -
        (150323855360 : K[X]) * a1 * a5 * h0 ^ 29 -
        (150323855360 : K[X]) * a2 * a4 * h0 ^ 29 -
        (75161927680 : K[X]) * a3 ^ 2 * h0 ^ 29 +
        (244276264960 : K[X]) * a1 * a6 * g1 * h0 ^ 25 -
        (106870865920 : K[X]) * a1 * g1 ^ 3 * h0 ^ 25 +
        (244276264960 : K[X]) * a2 * a5 * g1 * h0 ^ 25 +
        (244276264960 : K[X]) * a3 * a4 * g1 * h0 ^ 25 +
        (122138132480 : K[X]) * a2 * a6 ^ 2 * h0 ^ 21 -
        (320612597760 : K[X]) * a2 * a6 * g1 ^ 2 * h0 ^ 21 +
        (96851722240 : K[X]) * a2 * g1 ^ 4 * h0 ^ 21 +
        (244276264960 : K[X]) * a3 * a5 * a6 * h0 ^ 21 -
        (320612597760 : K[X]) * a3 * a5 * g1 ^ 2 * h0 ^ 21 +
        (122138132480 : K[X]) * a4 ^ 2 * a6 * h0 ^ 21 -
        (160306298880 : K[X]) * a4 ^ 2 * g1 ^ 2 * h0 ^ 21 +
        (122138132480 : K[X]) * a4 * a5 ^ 2 * h0 ^ 21 -
        (320612597760 : K[X]) * a3 * a6 ^ 2 * g1 * h0 ^ 17 +
        (387406888960 : K[X]) * a3 * a6 * g1 ^ 3 * h0 ^ 17 -
        (89587843072 : K[X]) * a3 * g1 ^ 5 * h0 ^ 17 -
        (641225195520 : K[X]) * a4 * a5 * a6 * g1 * h0 ^ 17 +
        (387406888960 : K[X]) * a4 * a5 * g1 ^ 3 * h0 ^ 17 -
        (106870865920 : K[X]) * a5 ^ 3 * g1 * h0 ^ 17 -
        (106870865920 : K[X]) * a4 * a6 ^ 3 * h0 ^ 13 +
        (581110333440 : K[X]) * a4 * a6 ^ 2 * g1 ^ 2 * h0 ^ 13 -
        (447939215360 : K[X]) * a4 * a6 * g1 ^ 4 * h0 ^ 13 +
        (83988602880 : K[X]) * a4 * g1 ^ 6 * h0 ^ 13 -
        (160306298880 : K[X]) * a5 ^ 2 * a6 ^ 2 * h0 ^ 13 +
        (581110333440 : K[X]) * a5 ^ 2 * a6 * g1 ^ 2 * h0 ^ 13 -
        (223969607680 : K[X]) * a5 ^ 2 * g1 ^ 4 * h0 ^ 13 +
        (387406888960 : K[X]) * a5 * a6 ^ 3 * g1 * h0 ^ 9 -
        (895878430720 : K[X]) * a5 * a6 ^ 2 * g1 ^ 3 * h0 ^ 9 +
        (503931617280 : K[X]) * a5 * a6 * g1 ^ 5 * h0 ^ 9 -
        (79489213440 : K[X]) * a5 * g1 ^ 7 * h0 ^ 9 +
        (19370344448 : K[X]) * a6 ^ 5 * h0 ^ 5 -
        (223969607680 : K[X]) * a6 ^ 4 * g1 ^ 2 * h0 ^ 5 +
        (419943014400 : K[X]) * a6 ^ 3 * g1 ^ 4 * h0 ^ 5 -
        (278212247040 : K[X]) * a6 ^ 2 * g1 ^ 6 * h0 ^ 5 +
        (75763156560 : K[X]) * a6 * g1 ^ 8 * h0 ^ 5 -
        (7260635837 : K[X]) * g1 ^ 10 * h0 ^ 5)

/-- Cleared thirteenth row of the square chamber, in factored form:
`h₀⁴` times the transport co-factor minus the pure `g₁, p₆` tridecic
block. -/
def alignedThirteenthSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedThirteenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ μ -
    (2900 : K[X]) * g1 *
      ((19258981 : K[X]) * g1 ^ 12 - (298574016 : K[X]) * a6 * g1 ^ 10 +
        (1809391168 : K[X]) * a6 ^ 2 * g1 ^ 8 -
        (5384491008 : K[X]) * a6 ^ 3 * g1 ^ 6 +
        (8054079488 : K[X]) * a6 ^ 4 * g1 ^ 4 -
        (5438963712 : K[X]) * a6 ^ 5 * g1 ^ 2 +
        (1145044992 : K[X]) * a6 ^ 6)

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the nonsquare-chamber thirteenth row
(`p₇ = H² g₂`, `H²⁶` peeled, `128 q₇ H` consumed): the `q₁` head is
`4398046511104 p₄ q₁ H¹⁵`. -/
def alignedThirteenthNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(27487790694400 : K[X]) * a0 * a3 * H ^ 16 -
    (27487790694400 : K[X]) * a1 * a2 * H ^ 16 +
    (21990232555520 : K[X]) * a0 * b5 * H ^ 15 +
    (17592186044416 : K[X]) * a1 * b4 * H ^ 15 +
    (13194139533312 : K[X]) * a2 * b3 * H ^ 15 +
    (8796093022208 : K[X]) * a3 * b2 * H ^ 15 +
    (4398046511104 : K[X]) * a4 * b1 * H ^ 15 +
    (13743895347200 : K[X]) * a0 * a4 * g2 * H ^ 14 +
    (13743895347200 : K[X]) * a1 * a3 * g2 * H ^ 14 +
    (6871947673600 : K[X]) * a2 ^ 2 * g2 * H ^ 14 -
    (16492674416640 : K[X]) * a0 * b6 * g2 * H ^ 13 -
    (13743895347200 : K[X]) * a1 * b5 * g2 * H ^ 13 -
    (10995116277760 : K[X]) * a2 * b4 * g2 * H ^ 13 -
    (8246337208320 : K[X]) * a3 * b3 * g2 * H ^ 13 -
    (5497558138880 : K[X]) * a4 * b2 * g2 * H ^ 13 -
    (2748779069440 : K[X]) * a5 * b1 * g2 * H ^ 13 -
    (6871947673600 : K[X]) * a0 * a5 * a6 * H ^ 12 +
    (7730941132800 : K[X]) * a0 * a5 * g2 ^ 2 * H ^ 12 +
    (17179869184000 : K[X]) * a1 * a4 * a6 * H ^ 12 -
    (11811160064000 : K[X]) * a1 * a4 * g2 ^ 2 * H ^ 12 -
    (1717986918400 : K[X]) * a1 * a5 ^ 2 * H ^ 12 +
    (17179869184000 : K[X]) * a2 * a3 * a6 * H ^ 12 -
    (11811160064000 : K[X]) * a2 * a3 * g2 ^ 2 * H ^ 12 +
    (20615843020800 : K[X]) * a2 * a4 * a5 * H ^ 12 +
    (10307921510400 : K[X]) * a3 ^ 2 * a5 * H ^ 12 +
    (22333829939200 : K[X]) * a3 * a4 ^ 2 * H ^ 12 -
    (16492674416640 : K[X]) * a1 * b6 * a6 * H ^ 11 +
    (13400297963520 : K[X]) * a1 * b6 * g2 ^ 2 * H ^ 11 -
    (16492674416640 : K[X]) * a2 * a5 * b6 * H ^ 11 -
    (13743895347200 : K[X]) * a2 * b5 * a6 * H ^ 11 +
    (11166914969600 : K[X]) * a2 * b5 * g2 ^ 2 * H ^ 11 -
    (16492674416640 : K[X]) * a3 * a4 * b6 * H ^ 11 -
    (13743895347200 : K[X]) * a3 * a5 * b5 * H ^ 11 -
    (10995116277760 : K[X]) * a3 * b4 * a6 * H ^ 11 +
    (8933531975680 : K[X]) * a3 * b4 * g2 ^ 2 * H ^ 11 -
    (6871947673600 : K[X]) * a4 ^ 2 * b5 * H ^ 11 -
    (10995116277760 : K[X]) * a4 * a5 * b4 * H ^ 11 -
    (8246337208320 : K[X]) * a4 * b3 * a6 * H ^ 11 +
    (6700148981760 : K[X]) * a4 * b3 * g2 ^ 2 * H ^ 11 -
    (4123168604160 : K[X]) * a5 ^ 2 * b3 * H ^ 11 -
    (5497558138880 : K[X]) * a5 * b2 * a6 * H ^ 11 +
    (4466765987840 : K[X]) * a5 * b2 * g2 ^ 2 * H ^ 11 -
    (1374389534720 : K[X]) * b1 * a6 ^ 2 * H ^ 11 +
    (2233382993920 : K[X]) * b1 * a6 * g2 ^ 2 * H ^ 11 -
    (488552529920 : K[X]) * b1 * g2 ^ 4 * H ^ 11 +
    (5153960755200 : K[X]) * a0 * a6 ^ 2 * g2 * H ^ 10 -
    (3435973836800 : K[X]) * a0 * a6 * g2 ^ 3 * H ^ 10 +
    (488552529920 : K[X]) * a0 * g2 ^ 5 * H ^ 10 +
    (10737418240000 : K[X]) * a1 * a5 * a6 * g2 * H ^ 10 -
    (5878736486400 : K[X]) * a1 * a5 * g2 ^ 3 * H ^ 10 -
    (28346784153600 : K[X]) * a2 * a4 * a6 * g2 * H ^ 10 +
    (11220602060800 : K[X]) * a2 * a4 * g2 ^ 3 * H ^ 10 +
    (5583457484800 : K[X]) * a2 * a5 ^ 2 * g2 * H ^ 10 -
    (14173392076800 : K[X]) * a3 ^ 2 * a6 * g2 * H ^ 10 +
    (5610301030400 : K[X]) * a3 ^ 2 * g2 ^ 3 * H ^ 10 -
    (27917287424000 : K[X]) * a3 * a4 * a5 * g2 * H ^ 10 -
    (11166914969600 : K[X]) * a4 ^ 3 * g2 * H ^ 10 +
    (26800595927040 : K[X]) * a2 * b6 * a6 * g2 * H ^ 9 -
    (11725260718080 : K[X]) * a2 * b6 * g2 ^ 3 * H ^ 9 +
    (26800595927040 : K[X]) * a3 * a5 * b6 * g2 * H ^ 9 +
    (22333829939200 : K[X]) * a3 * b5 * a6 * g2 * H ^ 9 -
    (9771050598400 : K[X]) * a3 * b5 * g2 ^ 3 * H ^ 9 +
    (13400297963520 : K[X]) * a4 ^ 2 * b6 * g2 * H ^ 9 +
    (22333829939200 : K[X]) * a4 * a5 * b5 * g2 * H ^ 9 +
    (17867063951360 : K[X]) * a4 * b4 * a6 * g2 * H ^ 9 -
    (7816840478720 : K[X]) * a4 * b4 * g2 ^ 3 * H ^ 9 +
    (8933531975680 : K[X]) * a5 ^ 2 * b4 * g2 * H ^ 9 +
    (13400297963520 : K[X]) * a5 * b3 * a6 * g2 * H ^ 9 -
    (5862630359040 : K[X]) * a5 * b3 * g2 ^ 3 * H ^ 9 +
    (4466765987840 : K[X]) * b2 * a6 ^ 2 * g2 * H ^ 9 -
    (3908420239360 : K[X]) * b2 * a6 * g2 ^ 3 * H ^ 9 +
    (708401168384 : K[X]) * b2 * g2 ^ 5 * H ^ 9 +
    (2791728742400 : K[X]) * a1 * a6 ^ 3 * H ^ 8 -
    (5757940531200 : K[X]) * a1 * a6 ^ 2 * g2 ^ 2 * H ^ 8 +
    (2671771648000 : K[X]) * a1 * a6 * g2 ^ 4 * H ^ 8 -
    (323475210240 : K[X]) * a1 * g2 ^ 6 * H ^ 8 +
    (5583457484800 : K[X]) * a2 * a5 * a6 ^ 2 * H ^ 8 -
    (13958643712000 : K[X]) * a2 * a5 * a6 * g2 ^ 2 * H ^ 8 +
    (4732852633600 : K[X]) * a2 * a5 * g2 ^ 4 * H ^ 8 -
    (13958643712000 : K[X]) * a3 * a4 * a6 ^ 2 * H ^ 8 +
    (37339371929600 : K[X]) * a3 * a4 * a6 * g2 ^ 2 * H ^ 8 -
    (10763422924800 : K[X]) * a3 * a4 * g2 ^ 4 * H ^ 8 +
    (2791728742400 : K[X]) * a3 * a5 ^ 2 * a6 * H ^ 8 -
    (8200703180800 : K[X]) * a3 * a5 ^ 2 * g2 ^ 2 * H ^ 8 -
    (16750372454400 : K[X]) * a4 ^ 2 * a5 * a6 * H ^ 8 +
    (17448304640000 : K[X]) * a4 ^ 2 * a5 * g2 ^ 2 * H ^ 8 +
    (13400297963520 : K[X]) * a3 * b6 * a6 ^ 2 * H ^ 7 -
    (35175782154240 : K[X]) * a3 * b6 * a6 * g2 ^ 2 * H ^ 7 +
    (10626017525760 : K[X]) * a3 * b6 * g2 ^ 4 * H ^ 7 +
    (26800595927040 : K[X]) * a4 * a5 * b6 * a6 * H ^ 7 -
    (35175782154240 : K[X]) * a4 * a5 * b6 * g2 ^ 2 * H ^ 7 +
    (11166914969600 : K[X]) * a4 * b5 * a6 ^ 2 * H ^ 7 -
    (29313151795200 : K[X]) * a4 * b5 * a6 * g2 ^ 2 * H ^ 7 +
    (8855014604800 : K[X]) * a4 * b5 * g2 ^ 4 * H ^ 7 +
    (4466765987840 : K[X]) * a5 ^ 3 * b6 * H ^ 7 +
    (11166914969600 : K[X]) * a5 ^ 2 * b5 * a6 * H ^ 7 -
    (14656575897600 : K[X]) * a5 ^ 2 * b5 * g2 ^ 2 * H ^ 7 +
    (8933531975680 : K[X]) * a5 * b4 * a6 ^ 2 * H ^ 7 -
    (23450521436160 : K[X]) * a5 * b4 * a6 * g2 ^ 2 * H ^ 7 +
    (7084011683840 : K[X]) * a5 * b4 * g2 ^ 4 * H ^ 7 +
    (2233382993920 : K[X]) * b3 * a6 ^ 3 * H ^ 7 -
    (8793945538560 : K[X]) * b3 * a6 ^ 2 * g2 ^ 2 * H ^ 7 +
    (5313008762880 : K[X]) * b3 * a6 * g2 ^ 4 * H ^ 7 -
    (819088850944 : K[X]) * b3 * g2 ^ 6 * H ^ 7 -
    (4885525299200 : K[X]) * a2 * a6 ^ 3 * g2 * H ^ 6 +
    (5801561292800 : K[X]) * a2 * a6 ^ 2 * g2 ^ 3 * H ^ 6 -
    (2049630535680 : K[X]) * a2 * a6 * g2 ^ 5 * H ^ 6 +
    (210504253440 : K[X]) * a2 * g2 ^ 7 * H ^ 6 -
    (12213813248000 : K[X]) * a3 * a5 * a6 ^ 2 * g2 * H ^ 6 +
    (15572611891200 : K[X]) * a3 * a5 * a6 * g2 ^ 3 * H ^ 6 -
    (3875977297920 : K[X]) * a3 * a5 * g2 ^ 5 * H ^ 6 +
    (19542101196800 : K[X]) * a4 ^ 2 * a6 ^ 2 * g2 * H ^ 6 -
    (23206245171200 : K[X]) * a4 ^ 2 * a6 * g2 ^ 3 * H ^ 6 +
    (5229038796800 : K[X]) * a4 ^ 2 * g2 ^ 5 * H ^ 6 -
    (9771050598400 : K[X]) * a4 * a5 ^ 2 * a6 * g2 * H ^ 6 +
    (9771050598400 : K[X]) * a4 * a5 ^ 2 * g2 ^ 3 * H ^ 6 -
    (4885525299200 : K[X]) * a5 ^ 4 * g2 * H ^ 6 -
    (35175782154240 : K[X]) * a4 * b6 * a6 ^ 2 * g2 * H ^ 5 +
    (42504070103040 : K[X]) * a4 * b6 * a6 * g2 ^ 3 * H ^ 5 -
    (9829066211328 : K[X]) * a4 * b6 * g2 ^ 5 * H ^ 5 -
    (35175782154240 : K[X]) * a5 ^ 2 * b6 * a6 * g2 * H ^ 5 +
    (21252035051520 : K[X]) * a5 ^ 2 * b6 * g2 ^ 3 * H ^ 5 -
    (29313151795200 : K[X]) * a5 * b5 * a6 ^ 2 * g2 * H ^ 5 +
    (35420058419200 : K[X]) * a5 * b5 * a6 * g2 ^ 3 * H ^ 5 -
    (8190888509440 : K[X]) * a5 * b5 * g2 ^ 5 * H ^ 5 -
    (7816840478720 : K[X]) * b4 * a6 ^ 3 * g2 * H ^ 5 +
    (14168023367680 : K[X]) * b4 * a6 ^ 2 * g2 ^ 3 * H ^ 5 -
    (6552710807552 : K[X]) * b4 * a6 * g2 ^ 5 * H ^ 5 +
    (877595197440 : K[X]) * b4 * g2 ^ 7 * H ^ 5 -
    (1832071987200 : K[X]) * a3 * a6 ^ 4 * H ^ 4 +
    (6870269952000 : K[X]) * a3 * a6 ^ 3 * g2 ^ 2 * H ^ 4 -
    (5453276774400 : K[X]) * a3 * a6 ^ 2 * g2 ^ 4 * H ^ 4 +
    (1518496645120 : K[X]) * a3 * a6 * g2 ^ 6 * H ^ 4 -
    (130553712640 : K[X]) * a3 * g2 ^ 8 * H ^ 4 -
    (4885525299200 : K[X]) * a4 * a5 * a6 ^ 3 * H ^ 4 +
    (20152791859200 : K[X]) * a4 * a5 * a6 ^ 2 * g2 ^ 2 * H ^ 4 -
    (16164218470400 : K[X]) * a4 * a5 * a6 * g2 ^ 4 * H ^ 4 +
    (3182270873600 : K[X]) * a4 * a5 * g2 ^ 6 * H ^ 4 -
    (9771050598400 : K[X]) * a5 ^ 3 * a6 ^ 2 * H ^ 4 +
    (37557475737600 : K[X]) * a5 ^ 3 * a6 * g2 ^ 2 * H ^ 4 -
    (15515359641600 : K[X]) * a5 ^ 3 * g2 ^ 4 * H ^ 4 -
    (11725260718080 : K[X]) * a5 * b6 * a6 ^ 3 * H ^ 3 +
    (63756105154560 : K[X]) * a5 * b6 * a6 ^ 2 * g2 ^ 2 * H ^ 3 -
    (49145331056640 : K[X]) * a5 * b6 * a6 * g2 ^ 4 * H ^ 3 +
    (9214749573120 : K[X]) * a5 * b6 * g2 ^ 6 * H ^ 3 -
    (2442762649600 : K[X]) * b5 * a6 ^ 4 * H ^ 3 +
    (17710029209600 : K[X]) * b5 * a6 ^ 3 * g2 ^ 2 * H ^ 3 -
    (20477221273600 : K[X]) * b5 * a6 ^ 2 * g2 ^ 4 * H ^ 3 +
    (7678957977600 : K[X]) * b5 * a6 * g2 ^ 6 * H ^ 3 -
    (908448153600 : K[X]) * b5 * g2 ^ 8 * H ^ 3 +
    (4580179968000 : K[X]) * a4 * a6 ^ 4 * g2 * H ^ 2 -
    (8320660275200 : K[X]) * a4 * a6 ^ 3 * g2 ^ 3 * H ^ 2 +
    (4773406310400 : K[X]) * a4 * a6 ^ 2 * g2 ^ 5 * H ^ 2 -
    (1051285913600 : K[X]) * a4 * a6 * g2 ^ 7 * H ^ 2 +
    (72133068800 : K[X]) * a4 * g2 ^ 9 * H ^ 2 +
    (37862821068800 : K[X]) * a5 ^ 2 * a6 ^ 3 * g2 * H ^ 2 -
    (85534860902400 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 ^ 3 * H ^ 2 +
    (48287501516800 : K[X]) * a5 ^ 2 * a6 * g2 ^ 5 * H ^ 2 -
    (7656103936000 : K[X]) * a5 ^ 2 * g2 ^ 7 * H ^ 2 +
    (10626017525760 : K[X]) * b6 * a6 ^ 4 * g2 * H -
    (32763554037760 : K[X]) * b6 * a6 ^ 3 * g2 ^ 3 * H +
    (27644248719360 : K[X]) * b6 * a6 ^ 2 * g2 ^ 5 * H -
    (8721102274560 : K[X]) * b6 * a6 * g2 ^ 7 * H +
    (923588956160 : K[X]) * b6 * g2 ^ 9 * H +
    (4427507302400 : K[X]) * a5 * a6 ^ 5 -
    (43721634611200 : K[X]) * a5 * a6 ^ 4 * g2 ^ 2 +
    (76132371660800 : K[X]) * a5 * a6 ^ 3 * g2 ^ 4 -
    (48313443942400 : K[X]) * a5 * a6 ^ 2 * g2 ^ 6 +
    (12753626496000 : K[X]) * a5 * a6 * g2 ^ 8 -
    (1189972451200 : K[X]) * a5 * g2 ^ 10 +
    Polynomial.C κ *
      (-(687194767360 : K[X]) * a0 * a5 * H ^ 15 -
        (687194767360 : K[X]) * a1 * a4 * H ^ 15 -
        (687194767360 : K[X]) * a2 * a3 * H ^ 15 +
        (515396075520 : K[X]) * a0 * a6 * g2 * H ^ 13 +
        (515396075520 : K[X]) * a1 * a5 * g2 * H ^ 13 +
        (515396075520 : K[X]) * a2 * a4 * g2 * H ^ 13 +
        (257698037760 : K[X]) * a3 ^ 2 * g2 * H ^ 13 +
        (558345748480 : K[X]) * a1 * a6 ^ 2 * H ^ 11 -
        (488552529920 : K[X]) * a1 * a6 * g2 ^ 2 * H ^ 11 +
        (15267266560 : K[X]) * a1 * g2 ^ 4 * H ^ 11 +
        (1116691496960 : K[X]) * a2 * a5 * a6 * H ^ 11 -
        (488552529920 : K[X]) * a2 * a5 * g2 ^ 2 * H ^ 11 +
        (1116691496960 : K[X]) * a3 * a4 * a6 * H ^ 11 -
        (488552529920 : K[X]) * a3 * a4 * g2 ^ 2 * H ^ 11 +
        (558345748480 : K[X]) * a3 * a5 ^ 2 * H ^ 11 +
        (558345748480 : K[X]) * a4 ^ 2 * a5 * H ^ 11 -
        (977105059840 : K[X]) * a2 * a6 ^ 2 * g2 * H ^ 9 +
        (488552529920 : K[X]) * a2 * a6 * g2 ^ 3 * H ^ 9 -
        (22137536512 : K[X]) * a2 * g2 ^ 5 * H ^ 9 -
        (1954210119680 : K[X]) * a3 * a5 * a6 * g2 * H ^ 9 +
        (488552529920 : K[X]) * a3 * a5 * g2 ^ 3 * H ^ 9 -
        (977105059840 : K[X]) * a4 ^ 2 * a6 * g2 * H ^ 9 +
        (244276264960 : K[X]) * a4 ^ 2 * g2 ^ 3 * H ^ 9 -
        (977105059840 : K[X]) * a4 * a5 ^ 2 * g2 * H ^ 9 -
        (488552529920 : K[X]) * a3 * a6 ^ 3 * H ^ 7 +
        (1374053990400 : K[X]) * a3 * a6 ^ 2 * g2 ^ 2 * H ^ 7 -
        (498094571520 : K[X]) * a3 * a6 * g2 ^ 4 * H ^ 7 +
        (25596526592 : K[X]) * a3 * g2 ^ 6 * H ^ 7 -
        (1465657589760 : K[X]) * a4 * a5 * a6 ^ 2 * H ^ 7 +
        (2748107980800 : K[X]) * a4 * a5 * a6 * g2 ^ 2 * H ^ 7 -
        (498094571520 : K[X]) * a4 * a5 * g2 ^ 4 * H ^ 7 -
        (488552529920 : K[X]) * a5 ^ 3 * a6 * H ^ 7 +
        (458017996800 : K[X]) * a5 ^ 3 * g2 ^ 2 * H ^ 7 +
        (1343519457280 : K[X]) * a4 * a6 ^ 3 * g2 * H ^ 5 -
        (1771002920960 : K[X]) * a4 * a6 ^ 2 * g2 ^ 3 * H ^ 5 +
        (511930531840 : K[X]) * a4 * a6 * g2 ^ 5 * H ^ 5 -
        (27424849920 : K[X]) * a4 * g2 ^ 7 * H ^ 5 +
        (2015279185920 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 * H ^ 5 -
        (1771002920960 : K[X]) * a5 ^ 2 * a6 * g2 ^ 3 * H ^ 5 +
        (255965265920 : K[X]) * a5 ^ 2 * g2 ^ 5 * H ^ 5 +
        (442750730240 : K[X]) * a5 * a6 ^ 4 * H ^ 3 -
        (2545816698880 : K[X]) * a5 * a6 ^ 3 * g2 ^ 2 * H ^ 3 +
        (2175704760320 : K[X]) * a5 * a6 ^ 2 * g2 ^ 4 * H ^ 3 -
        (527928360960 : K[X]) * a5 * a6 * g2 ^ 6 * H ^ 3 +
        (28389004800 : K[X]) * a5 * g2 ^ 8 * H ^ 3 -
        (332063047680 : K[X]) * a6 ^ 5 * g2 * H +
        (1023861063680 : K[X]) * a6 ^ 4 * g2 ^ 3 * H -
        (863882772480 : K[X]) * a6 ^ 3 * g2 ^ 5 * H +
        (272534446080 : K[X]) * a6 ^ 2 * g2 ^ 7 * H -
        (28862154880 : K[X]) * a6 * g2 ^ 9 * H)

/-- Cleared thirteenth row of the nonsquare chamber, in factored form:
`H²` times the transport co-factor minus the pure `g₂, p₆` tridecic
block. -/
def alignedThirteenthNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedThirteenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2
        b3 b4 b5 b6 κ -
    (2900 : K[X]) * g2 *
      ((19258981 : K[X]) * g2 ^ 12 - (298574016 : K[X]) * a6 * g2 ^ 10 +
        (1809391168 : K[X]) * a6 ^ 2 * g2 ^ 8 -
        (5384491008 : K[X]) * a6 ^ 3 * g2 ^ 6 +
        (8054079488 : K[X]) * a6 ^ 4 * g2 ^ 4 -
        (5438963712 : K[X]) * a6 ^ 5 * g2 ^ 2 +
        (1145044992 : K[X]) * a6 ^ 6)

/-! ## Square chamber -/

/-- In the square chamber the squared weight-ninety-one integral has a
polynomial square root with square core: `N₁₃ = ν₅ h₀⁹¹` with
`ν₅² = κ₁₂`.  The constant `ν₅` is preserved, not cleared. -/
theorem alignedSquareThirteenth_sqrt_810 {K : Type*} [Field K]
    [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₂ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hN2 : alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₁₂ * H ^ 91) :
    ∃ ν₅ : K, ν₅ ^ 2 = κ₁₂ ∧
      alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
          b6 b7 κ =
        Polynomial.C ν₅ * h0 ^ 91 := by
  set N : K[X] :=
    alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
      b6 b7 κ
    with hNdef
  have hdvd : (h0 ^ 91) ^ 2 ∣ N ^ 2 := by
    refine ⟨Polynomial.C κ₁₂, ?_⟩
    rw [hN2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₂ := by
    have h182 := hN2
    rw [hG, hHsq] at h182
    apply mul_left_cancel₀ (pow_ne_zero 182 hh0)
    linear_combination h182
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₁₂
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν₅, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν₅, ?_, ?_⟩
  · have hCν : Polynomial.C (ν₅ ^ 2) = Polynomial.C κ₁₂ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀⁵²` from `N₁₃ = ν₅ h₀⁹¹` on `H = h₀²`, `p₇ = h₀⁴ g₁`
and consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `-150323855360 p₀ p₆ h₀²⁴
+ 122138132480 p₀ g₁² h₀²⁴ - 150323855360 p₁ p₅ h₀²⁴
- 150323855360 p₂ p₄ h₀²⁴ - 75161927680 p₃² h₀²⁴
- 106870865920 p₁ g₁³ h₀²⁰ + 96851722240 p₂ g₁⁴ h₀¹⁶
- 89587843072 p₃ g₁⁵ h₀¹² + 83988602880 p₄ g₁⁶ h₀⁸
- 79489213440 p₅ g₁⁷ h₀⁴ + … - 7260635837 g₁¹⁰`, leaves the cleared
thirteenth row of the square chamber together with its factored
transport form. -/
theorem alignedSquareThirteenth_solved_810 {K : Type*} [Field K]
    [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ ν₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hN : alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C ν₅ * h0 ^ 91)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedThirteenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
        b5 b6 κ μ =
      Polynomial.C ν₅ * h0 ^ 39 ∧
    (2900 : K[X]) * g1 *
        ((19258981 : K[X]) * g1 ^ 12 - (298574016 : K[X]) * a6 * g1 ^ 10 +
          (1809391168 : K[X]) * a6 ^ 2 * g1 ^ 8 -
          (5384491008 : K[X]) * a6 ^ 3 * g1 ^ 6 +
          (8054079488 : K[X]) * a6 ^ 4 * g1 ^ 4 -
          (5438963712 : K[X]) * a6 ^ 5 * g1 ^ 2 +
          (1145044992 : K[X]) * a6 ^ 6) =
      h0 ^ 4 *
        (alignedThirteenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2
            b3 b4 b5 b6 κ μ -
          Polynomial.C ν₅ * h0 ^ 35) := by
  have hN' := hN
  simp only [alignedThirteenthDefect810, hHsq, hg] at hN'
  have hclear :
      alignedThirteenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ μ =
        Polynomial.C ν₅ * h0 ^ 39 := by
    simp only [alignedThirteenthSquareRow810, alignedThirteenthSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 52 hh0)
    linear_combination hN' -
      h0 ^ 52 *
        (-(150323855360 : K[X]) * a0 * a6 * h0 ^ 24 +
          (122138132480 : K[X]) * a0 * g1 ^ 2 * h0 ^ 24 -
          (150323855360 : K[X]) * a1 * a5 * h0 ^ 24 -
          (150323855360 : K[X]) * a2 * a4 * h0 ^ 24 -
          (75161927680 : K[X]) * a3 ^ 2 * h0 ^ 24 +
          (244276264960 : K[X]) * a1 * a6 * g1 * h0 ^ 20 -
          (106870865920 : K[X]) * a1 * g1 ^ 3 * h0 ^ 20 +
          (244276264960 : K[X]) * a2 * a5 * g1 * h0 ^ 20 +
          (244276264960 : K[X]) * a3 * a4 * g1 * h0 ^ 20 +
          (122138132480 : K[X]) * a2 * a6 ^ 2 * h0 ^ 16 -
          (320612597760 : K[X]) * a2 * a6 * g1 ^ 2 * h0 ^ 16 +
          (96851722240 : K[X]) * a2 * g1 ^ 4 * h0 ^ 16 +
          (244276264960 : K[X]) * a3 * a5 * a6 * h0 ^ 16 -
          (320612597760 : K[X]) * a3 * a5 * g1 ^ 2 * h0 ^ 16 +
          (122138132480 : K[X]) * a4 ^ 2 * a6 * h0 ^ 16 -
          (160306298880 : K[X]) * a4 ^ 2 * g1 ^ 2 * h0 ^ 16 +
          (122138132480 : K[X]) * a4 * a5 ^ 2 * h0 ^ 16 -
          (320612597760 : K[X]) * a3 * a6 ^ 2 * g1 * h0 ^ 12 +
          (387406888960 : K[X]) * a3 * a6 * g1 ^ 3 * h0 ^ 12 -
          (89587843072 : K[X]) * a3 * g1 ^ 5 * h0 ^ 12 -
          (641225195520 : K[X]) * a4 * a5 * a6 * g1 * h0 ^ 12 +
          (387406888960 : K[X]) * a4 * a5 * g1 ^ 3 * h0 ^ 12 -
          (106870865920 : K[X]) * a5 ^ 3 * g1 * h0 ^ 12 -
          (106870865920 : K[X]) * a4 * a6 ^ 3 * h0 ^ 8 +
          (581110333440 : K[X]) * a4 * a6 ^ 2 * g1 ^ 2 * h0 ^ 8 -
          (447939215360 : K[X]) * a4 * a6 * g1 ^ 4 * h0 ^ 8 +
          (83988602880 : K[X]) * a4 * g1 ^ 6 * h0 ^ 8 -
          (160306298880 : K[X]) * a5 ^ 2 * a6 ^ 2 * h0 ^ 8 +
          (581110333440 : K[X]) * a5 ^ 2 * a6 * g1 ^ 2 * h0 ^ 8 -
          (223969607680 : K[X]) * a5 ^ 2 * g1 ^ 4 * h0 ^ 8 +
          (387406888960 : K[X]) * a5 * a6 ^ 3 * g1 * h0 ^ 4 -
          (895878430720 : K[X]) * a5 * a6 ^ 2 * g1 ^ 3 * h0 ^ 4 +
          (503931617280 : K[X]) * a5 * a6 * g1 ^ 5 * h0 ^ 4 -
          (79489213440 : K[X]) * a5 * g1 ^ 7 * h0 ^ 4 +
          (19370344448 : K[X]) * a6 ^ 5 -
          (223969607680 : K[X]) * a6 ^ 4 * g1 ^ 2 +
          (419943014400 : K[X]) * a6 ^ 3 * g1 ^ 4 -
          (278212247040 : K[X]) * a6 ^ 2 * g1 ^ 6 +
          (75763156560 : K[X]) * a6 * g1 ^ 8 -
          (7260635837 : K[X]) * g1 ^ 10) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedThirteenthSquareRow810] at hclear
  linear_combination -hclear

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the squared
weight-ninety-one integral forces its constant to vanish, and with it
the whole thirteenth defect. -/
theorem alignedNonsquareThirteenth_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : k[X]} {κ κ₁₂ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hN2 : alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₁₂ * H ^ 91) :
    κ₁₂ = 0 ∧
      alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
          b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set N : k[X] :=
    alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
      b6 b7 κ
    with hNdef
  have hdvd : (H ^ 45) ^ 2 ∣ N ^ 2 := by
    refine ⟨Polynomial.C κ₁₂ * H, ?_⟩
    rw [hN2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₂ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 90 hH)
    have h90 := hN2
    rw [hG] at h90
    linear_combination h90
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₁₂ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk12 : κ₁₂ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hNzero : N = 0 := by
    have hsq : N ^ 2 = 0 := by
      rw [hN2, hk12]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk12, hNzero⟩

set_option maxHeartbeats 1600000000 in
/-- Peeling `H²⁶` from the vanished thirteenth defect on `p₇ = H² g₂`,
then consuming the previous factored quotient with the mate
`-150323855360 p₀ p₆ H¹² + 122138132480 p₀ g₂² H¹²
- 150323855360 p₁ p₅ H¹² - 150323855360 p₂ p₄ H¹² - 75161927680 p₃² H¹²
- 106870865920 p₁ g₂³ H¹⁰ + 96851722240 p₂ g₂⁴ H⁸ - 89587843072 p₃ g₂⁵ H⁶
+ 83988602880 p₄ g₂⁶ H⁴ - 79489213440 p₅ g₂⁷ H² + … - 7260635837 g₂¹⁰`,
leaves the cleared thirteenth row of the nonsquare chamber together
with its factored transport form. -/
theorem alignedNonsquareThirteenth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hN0 : alignedThirteenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ = 0)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedThirteenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ = 0 ∧
    (2900 : K[X]) * g2 *
        ((19258981 : K[X]) * g2 ^ 12 - (298574016 : K[X]) * a6 * g2 ^ 10 +
          (1809391168 : K[X]) * a6 ^ 2 * g2 ^ 8 -
          (5384491008 : K[X]) * a6 ^ 3 * g2 ^ 6 +
          (8054079488 : K[X]) * a6 ^ 4 * g2 ^ 4 -
          (5438963712 : K[X]) * a6 ^ 5 * g2 ^ 2 +
          (1145044992 : K[X]) * a6 ^ 6) =
      H ^ 2 *
        alignedThirteenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2
          b3 b4 b5 b6 κ := by
  have hN' := hN0
  simp only [alignedThirteenthDefect810, hg2] at hN'
  have hclear :
      alignedThirteenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ = 0 := by
    simp only [alignedThirteenthNonsquareRow810,
      alignedThirteenthNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 26 hH)
    rw [mul_zero]
    linear_combination hN' -
      H ^ 26 *
        (-(150323855360 : K[X]) * a0 * a6 * H ^ 12 +
          (122138132480 : K[X]) * a0 * g2 ^ 2 * H ^ 12 -
          (150323855360 : K[X]) * a1 * a5 * H ^ 12 -
          (150323855360 : K[X]) * a2 * a4 * H ^ 12 -
          (75161927680 : K[X]) * a3 ^ 2 * H ^ 12 +
          (244276264960 : K[X]) * a1 * a6 * g2 * H ^ 10 -
          (106870865920 : K[X]) * a1 * g2 ^ 3 * H ^ 10 +
          (244276264960 : K[X]) * a2 * a5 * g2 * H ^ 10 +
          (244276264960 : K[X]) * a3 * a4 * g2 * H ^ 10 +
          (122138132480 : K[X]) * a2 * a6 ^ 2 * H ^ 8 -
          (320612597760 : K[X]) * a2 * a6 * g2 ^ 2 * H ^ 8 +
          (96851722240 : K[X]) * a2 * g2 ^ 4 * H ^ 8 +
          (244276264960 : K[X]) * a3 * a5 * a6 * H ^ 8 -
          (320612597760 : K[X]) * a3 * a5 * g2 ^ 2 * H ^ 8 +
          (122138132480 : K[X]) * a4 ^ 2 * a6 * H ^ 8 -
          (160306298880 : K[X]) * a4 ^ 2 * g2 ^ 2 * H ^ 8 +
          (122138132480 : K[X]) * a4 * a5 ^ 2 * H ^ 8 -
          (320612597760 : K[X]) * a3 * a6 ^ 2 * g2 * H ^ 6 +
          (387406888960 : K[X]) * a3 * a6 * g2 ^ 3 * H ^ 6 -
          (89587843072 : K[X]) * a3 * g2 ^ 5 * H ^ 6 -
          (641225195520 : K[X]) * a4 * a5 * a6 * g2 * H ^ 6 +
          (387406888960 : K[X]) * a4 * a5 * g2 ^ 3 * H ^ 6 -
          (106870865920 : K[X]) * a5 ^ 3 * g2 * H ^ 6 -
          (106870865920 : K[X]) * a4 * a6 ^ 3 * H ^ 4 +
          (581110333440 : K[X]) * a4 * a6 ^ 2 * g2 ^ 2 * H ^ 4 -
          (447939215360 : K[X]) * a4 * a6 * g2 ^ 4 * H ^ 4 +
          (83988602880 : K[X]) * a4 * g2 ^ 6 * H ^ 4 -
          (160306298880 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 4 +
          (581110333440 : K[X]) * a5 ^ 2 * a6 * g2 ^ 2 * H ^ 4 -
          (223969607680 : K[X]) * a5 ^ 2 * g2 ^ 4 * H ^ 4 +
          (387406888960 : K[X]) * a5 * a6 ^ 3 * g2 * H ^ 2 -
          (895878430720 : K[X]) * a5 * a6 ^ 2 * g2 ^ 3 * H ^ 2 +
          (503931617280 : K[X]) * a5 * a6 * g2 ^ 5 * H ^ 2 -
          (79489213440 : K[X]) * a5 * g2 ^ 7 * H ^ 2 +
          (19370344448 : K[X]) * a6 ^ 5 -
          (223969607680 : K[X]) * a6 ^ 4 * g2 ^ 2 +
          (419943014400 : K[X]) * a6 ^ 3 * g2 ^ 4 -
          (278212247040 : K[X]) * a6 ^ 2 * g2 ^ 6 +
          (75763156560 : K[X]) * a6 * g2 ^ 8 -
          (7260635837 : K[X]) * g2 ^ 10) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedThirteenthNonsquareRow810] at hclear
  linear_combination -hclear

/-! ## Source-facing thirteenth-row packets -/

/-- Source-facing squared weight-ninety-one integral of a normalized
aligned scale-two `(8,10)` source: the degree-`4` row is consumed into
`N₁₃² = κ₁₂ H⁹¹` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedThirteenthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ κ₁₁ κ₁₂ : K),
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
          Polynomial.C κ₁₂ * H ^ 91 := by
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
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀, κ₁₁, κ₁₂,
    aligned_q9_solved_810 haligned, hM, hE4, hF2, hG, hI2, hJ, hL2,
    hN10, hN11, hN12, hN13⟩

/-- Exact square-chamber thirteenth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`4`
row gives `N₁₃ = ν₅ h₀⁹¹` with `ν₅² = κ₁₂`, the cleared thirteenth row
against `ν₅ h₀³⁹`, the carried root collapse `g₁ = p₆ = 0`, and the
carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedThirteenthFace_squareChamber_packet
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
    ∃ (κ μ κ₁₂ ν₅ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ν₅ ^ 2 = κ₁₂ ∧
        alignedThirteenthSquareRow810 h0 g1 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ μ =
          Polynomial.C ν₅ * h0 ^ 39 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₅ * h0 ^ 91 := by
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
  obtain ⟨κ₁₂, hN2⟩ :=
    alignedThirteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨ν₅, hν5, hN⟩ := alignedSquareThirteenth_sqrt_810 hh0 hHsq hN2
  obtain ⟨hsolved13, _hfact13⟩ :=
    alignedSquareThirteenth_solved_810 hh0 hHsq hp7 hN hcore
  exact ⟨κ, μ, κ₁₂, ν₅, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hν5,
    hsolved13, hcollapse, hdvdg1, hdvdp6, hN⟩

/-- Exact nonsquare-chamber thirteenth packet of a normalized aligned
scale-two `(8,10)` source: the squared weight-ninety-one constant
vanishes, the thirteenth defect is identically zero, and on top of
`p₇ = H² g₂` and the previous packet the consumed degree-`4` row gives
the cleared thirteenth row equal to zero, the carried root collapse
`g₂ = p₆ = 0` at every (simple) root of the core, and the carried
descents `H ∣ g₂`, `H ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedThirteenthFace_nonsquareChamber_packet
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
    ∃ (κ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        alignedThirteenthNonsquareRow810 H g2 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ = 0 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedThirteenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          0 := by
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
  obtain ⟨κ₁₂, hN2⟩ :=
    alignedThirteenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk12, hN0⟩ :=
    alignedNonsquareThirteenth_defect_eq_zero_810 hH hHdegree hnsq hN2
  obtain ⟨hclear13, _hfact13⟩ :=
    alignedNonsquareThirteenth_solved_810 hH hg2 hN0 hfac
  exact ⟨κ, g2, hg2, by rw [hq9, hg2]; ring, hclear13,
    hcollapse, hdvdg2, hdvdp6, hN0⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`4`
aligned row, carrying the factored transport of the tridecic block.
Neither chamber is excluded; in the square chamber `ν₅` is preserved,
in the nonsquare chamber the odd exponent forces the cleared row to
vanish.  No closure is claimed. -/
theorem normalized810ScaleTwo_alignedThirteenthFace_chamberDichotomy
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
      ∃ (κ μ ν₅ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (2900 : K[X]) * g1 *
              ((19258981 : K[X]) * g1 ^ 12 -
                (298574016 : K[X]) * p.coeff 6 * g1 ^ 10 +
                (1809391168 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 8 -
                (5384491008 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 6 +
                (8054079488 : K[X]) * p.coeff 6 ^ 4 * g1 ^ 4 -
                (5438963712 : K[X]) * p.coeff 6 ^ 5 * g1 ^ 2 +
                (1145044992 : K[X]) * p.coeff 6 ^ 6) =
            h0 ^ 4 *
              (alignedThirteenthSquareCof810 h0 g1 (p.coeff 0)
                  (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
                  (p.coeff 5) (p.coeff 6) (q.coeff 1) (q.coeff 2)
                  (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) κ μ -
                Polynomial.C ν₅ * h0 ^ 35) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (2900 : K[X]) * g2 *
              ((19258981 : K[X]) * g2 ^ 12 -
                (298574016 : K[X]) * p.coeff 6 * g2 ^ 10 +
                (1809391168 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 8 -
                (5384491008 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 6 +
                (8054079488 : K[X]) * p.coeff 6 ^ 4 * g2 ^ 4 -
                (5438963712 : K[X]) * p.coeff 6 ^ 5 * g2 ^ 2 +
                (1145044992 : K[X]) * p.coeff 6 ^ 6) =
            H ^ 2 *
              alignedThirteenthNonsquareCof810 H g2 (p.coeff 0)
                (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
                (p.coeff 5) (p.coeff 6) (q.coeff 1) (q.coeff 2)
                (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) κ ∧
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
      normalized810ScaleTwo_alignedThirteenthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₁₂, ν₅, g1, hp7, hq9, _hν5, hsolved13,
      hcollapse, hdvdg1, hdvdp6, _hN⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, ν₅, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedThirteenthSquareRow810] at hsolved13
    linear_combination -hsolved13
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedThirteenthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, hclear13, hcollapse,
      hdvdg2, hdvdp6, _hN0⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedThirteenthNonsquareRow810] at hclear13
    linear_combination -hclear13

/-- Chamber-independent root jet after the consumed degree-`4` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its tridecic content is absorbed by the
degree-`13` collapse (`alignedThirteenth_rootTridecic_absorbed_810`) —
and no new coefficient occurs, so the row re-ties `q₁, …, q₆` into the
cleared thirteenth row instead of killing anything new at the root. -/
theorem normalized810ScaleTwo_alignedThirteenthFace_rootJet
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
  normalized810ScaleTwo_alignedTwelfthFace_rootJet hsource haligned

#print axioms alignedThirteenthCoefficientJacobianRow_810
#print axioms alignedThirteenthDefect_weightedDerivative_identity_810
#print axioms alignedThirteenthDefectRow_eq_zero_810
#print axioms alignedThirteenthDefectPowerRelation_810
#print axioms alignedThirteenth_factored_rootBranch_810
#print axioms alignedThirteenth_rootTridecic_absorbed_810
#print axioms alignedSquareThirteenth_sqrt_810
#print axioms alignedSquareThirteenth_solved_810
#print axioms alignedNonsquareThirteenth_defect_eq_zero_810
#print axioms alignedNonsquareThirteenth_solved_810
#print axioms normalized810ScaleTwo_alignedThirteenthFace_packet
#print axioms normalized810ScaleTwo_alignedThirteenthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedThirteenthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedThirteenthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedThirteenthFace_rootJet

end Max11DegreeRoutes
