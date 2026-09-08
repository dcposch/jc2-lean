import Fable810ScaleTwoAlignedNinthFaceScratch

/-! # Tenth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedNinthFaceScratch` consumed the degree-`7`
aligned Keller row (the chamber-free `N₁₀ = κ₉ H³⁵`).  This file
consumes the next unused aligned row, the degree-`6` Jacobian
coefficient — the first aligned row that sees *no* new coefficient
(every `pᵢ` and `qⱼ` has been seen; internal names `alignedEleventh*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9`/`8`/`7` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, `H G' - 21 G H' = 0`,
`2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`, `2 H L' - 63 L H' = 0`,
`H N₁₀' - 35 N₁₀ H' = 0`, the degree-`6` row is the weighted
derivative of the weight-seventy-seven defect

`N₁₁ = -300647710720 p₀ p₅ H³⁶ - 300647710720 p₁ p₄ H³⁶
  - 300647710720 p₂ p₃ H³⁶ + 240518168576 p₀ q₇ H³⁵
  + 206158430208 p₁ q₆ H³⁵ + 171798691840 p₂ q₅ H³⁵
  + 137438953472 p₃ q₄ H³⁵ + 103079215104 p₄ q₃ H³⁵
  + 68719476736 p₅ q₂ H³⁵ + 34359738368 p₆ q₁ H³⁵ + …
  - 2058413175 p₇¹¹
  + κ (-7516192768 p₀ p₇ H³⁵ - 7516192768 p₁ p₆ H³⁵
       - 7516192768 p₂ p₅ H³⁵ - 7516192768 p₃ p₄ H³⁵ + …
       + 670890220 p₇⁹ H⁷)`

(the full one-hundred-forty-six-term expression is the literal body of
`alignedEleventhDefect810`; the defect is `q₀`-free — the single
monomial `q₀ p₇ H³⁵` of the weight-seventy-seven `q₀`-ansatz solves to
zero — and `q₀` enters the multiplier identity only through the
`N₁₀`-row correction `448 p₇ (H N₁₀' - 35 N₁₀ H')`), via the exact
multiplier identity

`68719476736 H³⁶ · row₆ = (2 H N₁₁' - 77 N₁₁ H')
  + (1879048192 p₀ H²⁸ + 1644167168 p₁ p₇ H²⁴ + 1644167168 p₂ p₆ H²⁴
     + 1644167168 p₃ p₅ H²⁴ + 822083584 p₄² H²⁴ - … + 805035 p₇⁸)
    (2 H D' - 21 D H')
  + (234881024 p₁ H²⁴ + 176160768 p₂ p₇ H²⁰ + 176160768 p₃ p₆ H²⁰
     + 176160768 p₄ p₅ H²⁰ - … - 339456 p₇⁷) (H E' - 14 E H')
  + (14680064 p₂ H²⁰ + 9175040 p₃ p₇ H¹⁶ + 9175040 p₄ p₆ H¹⁶
     + 4587520 p₅² H¹⁶ - … + 52668 p₇⁶) (2 H F' - 35 F H')
  + (7340032 p₃ H¹⁶ + 3670016 p₄ p₇ H¹² + 3670016 p₅ p₆ H¹²
     - 917504 p₅ p₇² H⁸ - 917504 p₆² p₇ H⁸ + 458752 p₆ p₇³ H⁴
     - 57344 p₇⁵) (H G' - 21 G H')
  + (57344 p₄ H¹² + 21504 p₅ p₇ H⁸ + 10752 p₆² H⁸ - 6720 p₆ p₇² H⁴
     + 910 p₇⁴) (2 H I' - 49 I H')
  + (14336 p₅ H⁸ + 3584 p₆ p₇ H⁴ - 448 p₇³) (H J' - 28 J H')
  + (448 p₆ H⁴ + 28 p₇²) (2 H L' - 63 L H')
  + 448 p₇ (H N₁₀' - 35 N₁₀ H')`.

The row sees neither `q₈` nor `q₉`, so — for the first time on this
face — *no* `N`- and *no* `C`-correction occurs at all: every
correction is a consumed tower row.  On the aligned face every
right-hand correction vanishes, so `2 H N₁₁' = 77 N₁₁ H'` and the
squared weight-seventy-seven first integral

`N₁₁² = κ₁₀ H⁷⁷`

holds for a preserved constant `κ₁₀`.  The exponent is odd, so —
exactly as for the degree-`14`, degree-`12`, degree-`10`, and
degree-`8` rows — the integral is **chambered**:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: `N₁₁ = ν₄ h₀⁷⁷` with
  `ν₄² = κ₁₀`; peeling `h₀⁴⁴` and consuming the previous factored
  quotient (`128 q₇ h₀²` solved, transported by the mate
  `1879048192 p₀ h₀²⁴ - 1644167168 p₁ g₁ h₀²⁰ - 1644167168 p₂ p₆ h₀¹⁶
  + 1541406720 p₂ g₁² h₀¹⁶ - 1644167168 p₃ p₅ h₀¹⁶ - 822083584 p₄² h₀¹⁶
  + … - 167722555 g₁⁸`) leaves the cleared eleventh row
  `alignedEleventhSquareRow810` against `ν₄ h₀³³`, and the factored
  transport `1840 g₁ (662935 g₁¹⁰ - 8788624 p₆ g₁⁸ + 43253184 p₆² g₁⁶
  - 96216064 p₆³ g₁⁴ + 92323840 p₆⁴ g₁² - 27525120 p₆⁵)
  = h₀⁴ (co-factor - ν₄ h₀²⁹)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₁₀ = 0` and `N₁₁ ≡ 0`.  With `p₇ = H² g₂`, peeling
  `H²²` and consuming the previous factored quotient (same mate) leaves
  the cleared eleventh row `alignedEleventhNonsquareRow810` equal to
  zero and the transport `1840 g₂ (662935 g₂¹⁰ - 8788624 p₆ g₂⁸
  + 43253184 p₆² g₂⁶ - 96216064 p₆³ g₂⁴ + 92323840 p₆⁴ g₂²
  - 27525120 p₆⁵) = H² · co-factor`.

At a root of the transport co-factor the honest root branch is the
root undecic `g = 0 ∨ 662935 g¹⁰ - 8788624 p₆ g⁸ + 43253184 p₆² g⁶
- 96216064 p₆³ g⁴ + 92323840 p₆⁴ g² - 27525120 p₆⁵ = 0`.  Like the
quintic through decic of the previous rows it adds *no new* root
information: the consumed degree-`13` row already collapsed
`g(a) = 0 ∧ p₆(a) = 0` at every core root, and that collapse absorbs
the undecic identically (`alignedEleventh_rootUndecic_absorbed_810`).
The chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` —
the row re-ties `q₁, …, q₇` into the cleared eleventh row (at `h₀³³`,
resp. `H¹⁵`) without killing anything new at the root.

No closure is claimed.  Both chambers remain open where not forced
(`κ₁₀ = 0` and `N₁₁ ≡ 0` are forced in the nonsquare chamber only,
exactly as `κ₈ = 0` was), the constants `κ`, `μ`, `κ₃`, `κ₄`, `κ₅`,
`κ₆`, `κ₇`, `κ₈`, `κ₉`, `κ₁₀ = ν₄²` are preserved where not forced,
the zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`,
`κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`, `κ₇ = 0`, `κ₈ = 0` in the square
chamber, `κ₉ = 0`, `κ₁₀ = 0` in the square chamber, `ν₄ = 0`) are not
excluded as polynomial identities, the deepened quotients `g₁/h₀`,
`p₆/h₀`, `g₂/H`, `p₆/H` from the degree-`13` face are still not
re-cleared through the tower here, the root undecic is recorded but
not excluded as an identity, and no individual vanishing of `p₀`,
`p₁`, `p₂`, `p₃`, `p₄`, `p₅`, `q₀`, `q₁`, `q₂`, `q₃`, `q₄`, `q₅`,
`q₆`, `q₇` is claimed.  The next unused Keller row on the aligned face
is the degree-`5` Jacobian coefficient (weight-eighty-four defect,
even exponent, hence chamber-free).  No total-degree or twice-prime
theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal degree-`6` Keller coefficient on the aligned face -/

/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`6` Jacobian coefficient, the first
aligned row that sees no new coefficient. -/
theorem alignedEleventhCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * q.coeff 1 +
        (p.coeff 5).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 0).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 1).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 2).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  rw [hC2, hC3, hC4, hC5, hC6, hC7]
  linear_combination hcoeff

/-! ## Aligned eleventh defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-seventy-seven defect of the degree-`6` aligned `(8,10)` row.
On the aligned face its square is a polynomial first integral of odd
weight seventy-seven, hence chambered.  No new coefficient occurs, and
the defect is `q₀`-free. -/
def alignedEleventhDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    K[X] :=
    -(300647710720 : K[X]) * a0 * a5 * H ^ 36 -
    (300647710720 : K[X]) * a1 * a4 * H ^ 36 -
    (300647710720 : K[X]) * a2 * a3 * H ^ 36 +
    (240518168576 : K[X]) * a0 * b7 * H ^ 35 +
    (206158430208 : K[X]) * a1 * b6 * H ^ 35 +
    (171798691840 : K[X]) * a2 * b5 * H ^ 35 +
    (137438953472 : K[X]) * a3 * b4 * H ^ 35 +
    (103079215104 : K[X]) * a4 * b3 * H ^ 35 +
    (68719476736 : K[X]) * a5 * b2 * H ^ 35 +
    (34359738368 : K[X]) * b1 * a6 * H ^ 35 -
    (75161927680 : K[X]) * a0 * a6 * a7 * H ^ 32 +
    (225485783040 : K[X]) * a1 * a5 * a7 * H ^ 32 -
    (18790481920 : K[X]) * a1 * a6 ^ 2 * H ^ 32 +
    (225485783040 : K[X]) * a2 * a4 * a7 * H ^ 32 +
    (263066746880 : K[X]) * a2 * a5 * a6 * H ^ 32 +
    (112742891520 : K[X]) * a3 ^ 2 * a7 * H ^ 32 +
    (263066746880 : K[X]) * a3 * a4 * a6 * H ^ 32 +
    (281857228800 : K[X]) * a3 * a5 ^ 2 * H ^ 32 +
    (281857228800 : K[X]) * a4 ^ 2 * a5 * H ^ 32 -
    (210453397504 : K[X]) * a1 * b7 * a7 * H ^ 31 -
    (210453397504 : K[X]) * a2 * b7 * a6 * H ^ 31 -
    (180388626432 : K[X]) * a2 * b6 * a7 * H ^ 31 -
    (210453397504 : K[X]) * a3 * a5 * b7 * H ^ 31 -
    (180388626432 : K[X]) * a3 * b6 * a6 * H ^ 31 -
    (150323855360 : K[X]) * a3 * b5 * a7 * H ^ 31 -
    (105226698752 : K[X]) * a4 ^ 2 * b7 * H ^ 31 -
    (180388626432 : K[X]) * a4 * a5 * b6 * H ^ 31 -
    (150323855360 : K[X]) * a4 * b5 * a6 * H ^ 31 -
    (120259084288 : K[X]) * a4 * b4 * a7 * H ^ 31 -
    (75161927680 : K[X]) * a5 ^ 2 * b5 * H ^ 31 -
    (120259084288 : K[X]) * a5 * b4 * a6 * H ^ 31 -
    (90194313216 : K[X]) * a5 * b3 * a7 * H ^ 31 -
    (45097156608 : K[X]) * b3 * a6 ^ 2 * H ^ 31 -
    (60129542144 : K[X]) * b2 * a6 * a7 * H ^ 31 -
    (15032385536 : K[X]) * b1 * a7 ^ 2 * H ^ 31 +
    (9395240960 : K[X]) * a0 * a7 ^ 3 * H ^ 28 +
    (68115496960 : K[X]) * a1 * a6 * a7 ^ 2 * H ^ 28 -
    (213741731840 : K[X]) * a2 * a5 * a7 ^ 2 * H ^ 28 +
    (70464307200 : K[X]) * a2 * a6 ^ 2 * a7 * H ^ 28 -
    (213741731840 : K[X]) * a3 * a4 * a7 ^ 2 * H ^ 28 -
    (422785843200 : K[X]) * a3 * a5 * a6 * a7 * H ^ 28 +
    (11744051200 : K[X]) * a3 * a6 ^ 3 * H ^ 28 -
    (211392921600 : K[X]) * a4 ^ 2 * a6 * a7 * H ^ 28 -
    (493250150400 : K[X]) * a4 * a5 ^ 2 * a7 * H ^ 28 -
    (246625075200 : K[X]) * a4 * a5 * a6 ^ 2 * H ^ 28 -
    (176160768000 : K[X]) * a5 ^ 3 * a6 * H ^ 28 +
    (197300060160 : K[X]) * a2 * b7 * a7 ^ 2 * H ^ 27 +
    (394600120320 : K[X]) * a3 * b7 * a6 * a7 * H ^ 27 +
    (169114337280 : K[X]) * a3 * b6 * a7 ^ 2 * H ^ 27 +
    (394600120320 : K[X]) * a4 * a5 * b7 * a7 * H ^ 27 +
    (197300060160 : K[X]) * a4 * b7 * a6 ^ 2 * H ^ 27 +
    (338228674560 : K[X]) * a4 * b6 * a6 * a7 * H ^ 27 +
    (140928614400 : K[X]) * a4 * b5 * a7 ^ 2 * H ^ 27 +
    (197300060160 : K[X]) * a5 ^ 2 * b7 * a6 * H ^ 27 +
    (169114337280 : K[X]) * a5 ^ 2 * b6 * a7 * H ^ 27 +
    (169114337280 : K[X]) * a5 * b6 * a6 ^ 2 * H ^ 27 +
    (281857228800 : K[X]) * a5 * b5 * a6 * a7 * H ^ 27 +
    (112742891520 : K[X]) * a5 * b4 * a7 ^ 2 * H ^ 27 +
    (46976204800 : K[X]) * b5 * a6 ^ 3 * H ^ 27 +
    (112742891520 : K[X]) * b4 * a6 ^ 2 * a7 * H ^ 27 +
    (84557168640 : K[X]) * b3 * a6 * a7 ^ 2 * H ^ 27 +
    (18790481920 : K[X]) * b2 * a7 ^ 3 * H ^ 27 -
    (6973030400 : K[X]) * a1 * a7 ^ 4 * H ^ 24 -
    (64592281600 : K[X]) * a2 * a6 * a7 ^ 3 * H ^ 24 +
    (205520896000 : K[X]) * a3 * a5 * a7 ^ 3 * H ^ 24 -
    (116706508800 : K[X]) * a3 * a6 ^ 2 * a7 ^ 2 * H ^ 24 +
    (102760448000 : K[X]) * a4 ^ 2 * a7 ^ 3 * H ^ 24 +
    (576926515200 : K[X]) * a4 * a5 * a6 * a7 ^ 2 * H ^ 24 -
    (67528294400 : K[X]) * a4 * a6 ^ 3 * a7 * H ^ 24 +
    (231211008000 : K[X]) * a5 ^ 3 * a7 ^ 2 * H ^ 24 +
    (303877324800 : K[X]) * a5 ^ 2 * a6 ^ 2 * a7 * H ^ 24 -
    (8441036800 : K[X]) * a5 * a6 ^ 4 * H ^ 24 -
    (189079224320 : K[X]) * a3 * b7 * a7 ^ 3 * H ^ 23 -
    (567237672960 : K[X]) * a4 * b7 * a6 * a7 ^ 2 * H ^ 23 -
    (162067906560 : K[X]) * a4 * b6 * a7 ^ 3 * H ^ 23 -
    (283618836480 : K[X]) * a5 ^ 2 * b7 * a7 ^ 2 * H ^ 23 -
    (567237672960 : K[X]) * a5 * b7 * a6 ^ 2 * a7 * H ^ 23 -
    (486203719680 : K[X]) * a5 * b6 * a6 * a7 ^ 2 * H ^ 23 -
    (135056588800 : K[X]) * a5 * b5 * a7 ^ 3 * H ^ 23 -
    (47269806080 : K[X]) * b7 * a6 ^ 4 * H ^ 23 -
    (162067906560 : K[X]) * b6 * a6 ^ 3 * a7 * H ^ 23 -
    (202584883200 : K[X]) * b5 * a6 ^ 2 * a7 ^ 2 * H ^ 23 -
    (108045271040 : K[X]) * b4 * a6 * a7 ^ 3 * H ^ 23 -
    (20258488320 : K[X]) * b3 * a7 ^ 4 * H ^ 23 +
    (5486673920 : K[X]) * a2 * a7 ^ 5 * H ^ 20 +
    (62252646400 : K[X]) * a3 * a6 * a7 ^ 4 * H ^ 20 -
    (199419494400 : K[X]) * a4 * a5 * a7 ^ 4 * H ^ 20 +
    (160379699200 : K[X]) * a4 * a6 ^ 2 * a7 ^ 3 * H ^ 20 -
    (362964582400 : K[X]) * a5 ^ 2 * a6 * a7 ^ 3 * H ^ 20 +
    (162489958400 : K[X]) * a5 * a6 ^ 3 * a7 ^ 2 * H ^ 20 +
    (65418035200 : K[X]) * a6 ^ 5 * a7 * H ^ 20 +
    (183170498560 : K[X]) * a4 * b7 * a7 ^ 4 * H ^ 19 +
    (732681994240 : K[X]) * a5 * b7 * a6 * a7 ^ 3 * H ^ 19 +
    (157003284480 : K[X]) * a5 * b6 * a7 ^ 4 * H ^ 19 +
    (366340997120 : K[X]) * b7 * a6 ^ 3 * a7 ^ 2 * H ^ 19 +
    (314006568960 : K[X]) * b6 * a6 ^ 2 * a7 ^ 3 * H ^ 19 +
    (130836070400 : K[X]) * b5 * a6 * a7 ^ 4 * H ^ 19 +
    (20933771264 : K[X]) * b4 * a7 ^ 5 * H ^ 19 -
    (4497489920 : K[X]) * a3 * a7 ^ 6 * H ^ 16 -
    (60511682560 : K[X]) * a4 * a6 * a7 ^ 5 * H ^ 16 +
    (97309327360 : K[X]) * a5 ^ 2 * a7 ^ 5 * H ^ 16 -
    (202387046400 : K[X]) * a5 * a6 ^ 2 * a7 ^ 4 * H ^ 16 -
    (286203904000 : K[X]) * a6 ^ 4 * a7 ^ 3 * H ^ 16 -
    (178591236096 : K[X]) * a5 * b7 * a7 ^ 5 * H ^ 15 -
    (446478090240 : K[X]) * b7 * a6 ^ 2 * a7 ^ 4 * H ^ 15 -
    (153078202368 : K[X]) * b6 * a6 * a7 ^ 5 * H ^ 15 -
    (21260861440 : K[X]) * b5 * a7 ^ 6 * H ^ 15 +
    (3796582400 : K[X]) * a4 * a7 ^ 7 * H ^ 12 +
    (59131770880 : K[X]) * a5 * a6 * a7 ^ 6 * H ^ 12 +
    (330872156160 : K[X]) * a6 ^ 3 * a7 ^ 5 * H ^ 12 +
    (174870585344 : K[X]) * b7 * a6 * a7 ^ 6 * H ^ 11 +
    (21412724736 : K[X]) * b6 * a7 ^ 7 * H ^ 11 -
    (3276035360 : K[X]) * a5 * a7 ^ 8 * H ^ 8 -
    (151673466880 : K[X]) * a6 ^ 2 * a7 ^ 7 * H ^ 8 -
    (21468487040 : K[X]) * b7 * a7 ^ 8 * H ^ 7 +
    (29710852600 : K[X]) * a6 * a7 ^ 9 * H ^ 4 -
    (2058413175 : K[X]) * a7 ^ 11 +
    Polynomial.C κ *
      (-(7516192768 : K[X]) * a0 * a7 * H ^ 35 -
        (7516192768 : K[X]) * a1 * a6 * H ^ 35 -
        (7516192768 : K[X]) * a2 * a5 * H ^ 35 -
        (7516192768 : K[X]) * a3 * a4 * H ^ 35 +
        (7046430720 : K[X]) * a1 * a7 ^ 2 * H ^ 31 +
        (14092861440 : K[X]) * a2 * a6 * a7 * H ^ 31 +
        (14092861440 : K[X]) * a3 * a5 * a7 * H ^ 31 +
        (7046430720 : K[X]) * a3 * a6 ^ 2 * H ^ 31 +
        (7046430720 : K[X]) * a4 ^ 2 * a7 * H ^ 31 +
        (14092861440 : K[X]) * a4 * a5 * a6 * H ^ 31 +
        (2348810240 : K[X]) * a5 ^ 3 * H ^ 31 -
        (6752829440 : K[X]) * a2 * a7 ^ 3 * H ^ 27 -
        (20258488320 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 27 -
        (20258488320 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 27 -
        (20258488320 : K[X]) * a4 * a6 ^ 2 * a7 * H ^ 27 -
        (20258488320 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 27 -
        (6752829440 : K[X]) * a5 * a6 ^ 3 * H ^ 27 +
        (6541803520 : K[X]) * a3 * a7 ^ 4 * H ^ 23 +
        (26167214080 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 23 +
        (13083607040 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 23 +
        (39250821120 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 23 +
        (6541803520 : K[X]) * a6 ^ 4 * a7 * H ^ 23 -
        (6378258432 : K[X]) * a4 * a7 ^ 5 * H ^ 19 -
        (31891292160 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 19 -
        (21260861440 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 19 +
        (6245378048 : K[X]) * a5 * a7 ^ 6 * H ^ 15 +
        (18736134144 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 15 -
        (6133853440 : K[X]) * a6 * a7 ^ 7 * H ^ 11 +
        (670890220 : K[X]) * a7 ^ 9 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`6` Jacobian expression with the
weighted derivative of `N₁₁`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` through
degree-`7` rows.  The row sees neither `q₈` nor `q₉`, so — for the
first time on this face — no `N`- and no `C`-correction occurs at all:
every correction is a consumed tower row, and `q₀` couples only
through the `N₁₀`-row correction. -/
theorem alignedEleventhDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    (68719476736 : K[X]) * H ^ 36 *
        (a6.derivative * b1 +
          a5.derivative * (b2 * (2 : K[X])) +
          a4.derivative * (b3 * (3 : K[X])) +
          a3.derivative * (b4 * (4 : K[X])) +
          a2.derivative * (b5 * (5 : K[X])) +
          a1.derivative * (b6 * (6 : K[X])) +
          a0.derivative * (b7 * (7 : K[X])) -
        ((a7 * (7 : K[X])) * b0.derivative +
          (a6 * (6 : K[X])) * b1.derivative +
          (a5 * (5 : K[X])) * b2.derivative +
          (a4 * (4 : K[X])) * b3.derivative +
          (a3 * (3 : K[X])) * b4.derivative +
          (a2 * (2 : K[X])) * b5.derivative +
          a1 * b6.derivative)) =
      ((2 : K[X]) * H *
          (alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ).derivative -
        (77 : K[X]) *
          alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
            b4 b5 b6 b7 κ * H.derivative) +
        ((1879048192 : K[X]) * a0 * H ^ 28 +
            (1644167168 : K[X]) * a1 * a7 * H ^ 24 +
            (1644167168 : K[X]) * a2 * a6 * H ^ 24 +
            (1644167168 : K[X]) * a3 * a5 * H ^ 24 +
            (822083584 : K[X]) * a4 ^ 2 * H ^ 24 -
            (102760448 : K[X]) * a2 * a7 ^ 2 * H ^ 20 -
            (205520896 : K[X]) * a3 * a6 * a7 * H ^ 20 -
            (205520896 : K[X]) * a4 * a5 * a7 * H ^ 20 -
            (102760448 : K[X]) * a4 * a6 ^ 2 * H ^ 20 -
            (102760448 : K[X]) * a5 ^ 2 * a6 * H ^ 20 +
            (38535168 : K[X]) * a3 * a7 ^ 3 * H ^ 16 +
            (115605504 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 16 +
            (57802752 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 16 +
            (115605504 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 16 +
            (9633792 : K[X]) * a6 ^ 4 * H ^ 16 -
            (20471808 : K[X]) * a4 * a7 ^ 4 * H ^ 12 -
            (81887232 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 12 -
            (40943616 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 12 +
            (12794880 : K[X]) * a5 * a7 ^ 5 * H ^ 8 +
            (31987200 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 8 -
            (8796480 : K[X]) * a6 * a7 ^ 6 * H ^ 4 +
            (805035 : K[X]) * a7 ^ 8) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((234881024 : K[X]) * a1 * H ^ 24 +
            (176160768 : K[X]) * a2 * a7 * H ^ 20 +
            (176160768 : K[X]) * a3 * a6 * H ^ 20 +
            (176160768 : K[X]) * a4 * a5 * H ^ 20 -
            (22020096 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
            (44040192 : K[X]) * a4 * a6 * a7 * H ^ 16 -
            (22020096 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
            (22020096 : K[X]) * a5 * a6 ^ 2 * H ^ 16 +
            (9175040 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
            (27525120 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
            (9175040 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
            (5160960 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
            (10321920 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
            (3354624 : K[X]) * a6 * a7 ^ 5 * H ^ 4 -
            (339456 : K[X]) * a7 ^ 7) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((14680064 : K[X]) * a2 * H ^ 20 +
            (9175040 : K[X]) * a3 * a7 * H ^ 16 +
            (9175040 : K[X]) * a4 * a6 * H ^ 16 +
            (4587520 : K[X]) * a5 ^ 2 * H ^ 16 -
            (1720320 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (3440640 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (573440 : K[X]) * a6 ^ 3 * H ^ 12 +
            (788480 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (1182720 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (468160 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (52668 : K[X]) * a7 ^ 6) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((7340032 : K[X]) * a3 * H ^ 16 +
            (3670016 : K[X]) * a4 * a7 * H ^ 12 +
            (3670016 : K[X]) * a5 * a6 * H ^ 12 -
            (917504 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (917504 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (458752 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (57344 : K[X]) * a7 ^ 5) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((57344 : K[X]) * a4 * H ^ 12 +
            (21504 : K[X]) * a5 * a7 * H ^ 8 +
            (10752 : K[X]) * a6 ^ 2 * H ^ 8 -
            (6720 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (910 : K[X]) * a7 ^ 4) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        ((14336 : K[X]) * a5 * H ^ 8 +
            (3584 : K[X]) * a6 * a7 * H ^ 4 -
            (448 : K[X]) * a7 ^ 3) *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        ((448 : K[X]) * a6 * H ^ 4 +
            (28 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ).derivative -
            (63 : K[X]) *
              alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        (448 : K[X]) * a7 *
          (H * (alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ).derivative -
            (35 : K[X]) *
              alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2
                b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedEleventhDefect810, alignedTenthDefect810,
    alignedNinthDefect810, alignedEighthDefect810, alignedSeventhDefect810,
    alignedSixthDefect810, alignedFifthDefect810, alignedFourthDefect810,
    alignedThirdDefect810,
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
degree-`7` rows, the degree-`6` row is the weighted derivative
`2 H N₁₁' - 77 N₁₁ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (77 : K[X]) *
        alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_810 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7] at hrow
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
  have hid := alignedEleventhDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 0) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) κ
  rw [hrow, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ, hrowL, hrowN]
    at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-seventy-seven polynomial first integral of the
aligned `(8,10)` eleventh defect: `N₁₁² = κ₁₀ H⁷⁷`.  The exponent is
odd, so the integral is chambered. -/
theorem alignedEleventhDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 77 := by
  let N : K[X] :=
    alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * N.derivative -
        (77 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      alignedEleventhDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC77 : Polynomial.C (77 : K) = (77 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (N ^ 2) (H ^ 77) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      N ^ 2 * (Polynomial.C (77 : K) * H ^ (77 - 1) * H.derivative) -
          Polynomial.C (2 : K) * N ^ (2 - 1) * N.derivative * H ^ 77 =
          N * H ^ 76 *
            (Polynomial.C (77 : K) * N * H.derivative -
              Polynomial.C (2 : K) * H * N.derivative) := by
        ring
      _ = 0 := by
        rw [hC77, hC2]
        have hfac :
            (77 : K[X]) * N * H.derivative -
              (2 : K[X]) * H * N.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 77 hH) hW

/-! ## Root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport eleventh row at a root of its
co-factor: either the descent quotient vanishes there, or the even
decic core `662935 g¹⁰ - 8788624 p₆ g⁸ + 43253184 p₆² g⁶
- 96216064 p₆³ g⁴ + 92323840 p₆⁴ g² - 27525120 p₆⁵` does.  Neither
branch is excluded. -/
theorem alignedEleventh_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (1840 : K[X]) * g *
        ((662935 : K[X]) * g ^ 10 - (8788624 : K[X]) * a6 * g ^ 8 +
          (43253184 : K[X]) * a6 ^ 2 * g ^ 6 -
          (96216064 : K[X]) * a6 ^ 3 * g ^ 4 +
          (92323840 : K[X]) * a6 ^ 4 * g ^ 2 -
          (27525120 : K[X]) * a6 ^ 5) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨
      662935 * (g.eval a) ^ 10 - 8788624 * a6.eval a * (g.eval a) ^ 8 +
        43253184 * (a6.eval a) ^ 2 * (g.eval a) ^ 6 -
        96216064 * (a6.eval a) ^ 3 * (g.eval a) ^ 4 +
        92323840 * (a6.eval a) ^ 4 * (g.eval a) ^ 2 -
        27525120 * (a6.eval a) ^ 5 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h1840g | hdecic
  · exact Or.inl
      ((mul_eq_zero.mp h1840g).resolve_left
        (by norm_num : (1840 : K) ≠ 0))
  · exact Or.inr (by linear_combination hdecic)

/-- The root undecic of the consumed degree-`6` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the eleventh row adds no new root
constraint. -/
theorem alignedEleventh_rootUndecic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    1840 * G * (662935 * G ^ 10 - 8788624 * P6 * G ^ 8 +
      43253184 * P6 ^ 2 * G ^ 6 - 96216064 * P6 ^ 3 * G ^ 4 +
      92323840 * P6 ^ 4 * G ^ 2 - 27525120 * P6 ^ 5) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared eleventh rows and transport co-factors -/

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the square-chamber eleventh row (`H = h₀²`,
`p₇ = h₀⁴ g₁`, `h₀⁴⁴` peeled, `128 q₇ h₀²` consumed): `q₁` sits at
`h₀²⁹` here, i.e. at `h₀³³` in the cleared row. -/
def alignedEleventhSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
    -(300647710720 : K[X]) * a1 * a4 * h0 ^ 24 -
    (300647710720 : K[X]) * a2 * a3 * h0 ^ 24 +
    (206158430208 : K[X]) * a1 * b6 * h0 ^ 22 +
    (171798691840 : K[X]) * a2 * b5 * h0 ^ 22 +
    (137438953472 : K[X]) * a3 * b4 * h0 ^ 22 +
    (103079215104 : K[X]) * a4 * b3 * h0 ^ 22 +
    (68719476736 : K[X]) * a5 * b2 * h0 ^ 22 +
    (34359738368 : K[X]) * b1 * a6 * h0 ^ 22 -
    (15032385536 : K[X]) * b1 * g1 ^ 2 * h0 ^ 22 -
    (37580963840 : K[X]) * a1 * a5 * g1 * h0 ^ 20 +
    (225485783040 : K[X]) * a2 * a4 * g1 * h0 ^ 20 +
    (112742891520 : K[X]) * a3 ^ 2 * g1 * h0 ^ 20 -
    (180388626432 : K[X]) * a2 * b6 * g1 * h0 ^ 18 -
    (150323855360 : K[X]) * a3 * b5 * g1 * h0 ^ 18 -
    (120259084288 : K[X]) * a4 * b4 * g1 * h0 ^ 18 -
    (90194313216 : K[X]) * a5 * b3 * g1 * h0 ^ 18 -
    (60129542144 : K[X]) * b2 * a6 * g1 * h0 ^ 18 +
    (18790481920 : K[X]) * b2 * g1 ^ 3 * h0 ^ 18 -
    (18790481920 : K[X]) * a1 * a6 ^ 2 * h0 ^ 16 +
    (2348810240 : K[X]) * a1 * a6 * g1 ^ 2 * h0 ^ 16 +
    (1247805440 : K[X]) * a1 * g1 ^ 4 * h0 ^ 16 +
    (32883343360 : K[X]) * a2 * a5 * g1 ^ 2 * h0 ^ 16 +
    (263066746880 : K[X]) * a3 * a4 * a6 * h0 ^ 16 -
    (213741731840 : K[X]) * a3 * a4 * g1 ^ 2 * h0 ^ 16 +
    (18790481920 : K[X]) * a3 * a5 ^ 2 * h0 ^ 16 +
    (150323855360 : K[X]) * a4 ^ 2 * a5 * h0 ^ 16 -
    (180388626432 : K[X]) * a3 * b6 * a6 * h0 ^ 14 +
    (169114337280 : K[X]) * a3 * b6 * g1 ^ 2 * h0 ^ 14 -
    (180388626432 : K[X]) * a4 * a5 * b6 * h0 ^ 14 -
    (150323855360 : K[X]) * a4 * b5 * a6 * h0 ^ 14 +
    (140928614400 : K[X]) * a4 * b5 * g1 ^ 2 * h0 ^ 14 -
    (75161927680 : K[X]) * a5 ^ 2 * b5 * h0 ^ 14 -
    (120259084288 : K[X]) * a5 * b4 * a6 * h0 ^ 14 +
    (112742891520 : K[X]) * a5 * b4 * g1 ^ 2 * h0 ^ 14 -
    (45097156608 : K[X]) * b3 * a6 ^ 2 * h0 ^ 14 +
    (84557168640 : K[X]) * b3 * a6 * g1 ^ 2 * h0 ^ 14 -
    (20258488320 : K[X]) * b3 * g1 ^ 4 * h0 ^ 14 +
    (4697620480 : K[X]) * a2 * a6 ^ 2 * g1 * h0 ^ 12 +
    (5284823040 : K[X]) * a2 * a6 * g1 ^ 3 * h0 ^ 12 -
    (2220359680 : K[X]) * a2 * g1 ^ 5 * h0 ^ 12 +
    (4697620480 : K[X]) * a3 * a5 * a6 * g1 * h0 ^ 12 -
    (22607298560 : K[X]) * a3 * a5 * g1 ^ 3 * h0 ^ 12 -
    (244276264960 : K[X]) * a4 ^ 2 * a6 * g1 * h0 ^ 12 +
    (106870865920 : K[X]) * a4 ^ 2 * g1 ^ 3 * h0 ^ 12 +
    (338228674560 : K[X]) * a4 * b6 * a6 * g1 * h0 ^ 10 -
    (162067906560 : K[X]) * a4 * b6 * g1 ^ 3 * h0 ^ 10 +
    (169114337280 : K[X]) * a5 ^ 2 * b6 * g1 * h0 ^ 10 +
    (281857228800 : K[X]) * a5 * b5 * a6 * g1 * h0 ^ 10 -
    (135056588800 : K[X]) * a5 * b5 * g1 ^ 3 * h0 ^ 10 +
    (112742891520 : K[X]) * b4 * a6 ^ 2 * g1 * h0 ^ 10 -
    (108045271040 : K[X]) * b4 * a6 * g1 ^ 3 * h0 ^ 10 +
    (20933771264 : K[X]) * b4 * g1 ^ 5 * h0 ^ 10 +
    (11744051200 : K[X]) * a3 * a6 ^ 3 * h0 ^ 8 +
    (6606028800 : K[X]) * a3 * a6 ^ 2 * g1 ^ 2 * h0 ^ 8 -
    (12248678400 : K[X]) * a3 * a6 * g1 ^ 4 * h0 ^ 8 +
    (2888417280 : K[X]) * a3 * g1 ^ 6 * h0 ^ 8 -
    (8808038400 : K[X]) * a4 * a5 * a6 * g1 ^ 2 * h0 ^ 8 +
    (14129561600 : K[X]) * a4 * a5 * g1 ^ 4 * h0 ^ 8 +
    (70464307200 : K[X]) * a5 ^ 3 * a6 * h0 ^ 8 -
    (123312537600 : K[X]) * a5 ^ 3 * g1 ^ 2 * h0 ^ 8 +
    (169114337280 : K[X]) * a5 * b6 * a6 ^ 2 * h0 ^ 6 -
    (486203719680 : K[X]) * a5 * b6 * a6 * g1 ^ 2 * h0 ^ 6 +
    (157003284480 : K[X]) * a5 * b6 * g1 ^ 4 * h0 ^ 6 +
    (46976204800 : K[X]) * b5 * a6 ^ 3 * h0 ^ 6 -
    (202584883200 : K[X]) * b5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 6 +
    (130836070400 : K[X]) * b5 * a6 * g1 ^ 4 * h0 ^ 6 -
    (21260861440 : K[X]) * b5 * g1 ^ 6 * h0 ^ 6 -
    (5872025600 : K[X]) * a4 * a6 ^ 3 * g1 * h0 ^ 4 -
    (24589107200 : K[X]) * a4 * a6 ^ 2 * g1 ^ 3 * h0 ^ 4 +
    (18886819840 : K[X]) * a4 * a6 * g1 ^ 5 * h0 ^ 4 -
    (3358515200 : K[X]) * a4 * g1 ^ 7 * h0 ^ 4 -
    (343513497600 : K[X]) * a5 ^ 2 * a6 ^ 2 * g1 * h0 ^ 4 +
    (456549990400 : K[X]) * a5 ^ 2 * a6 * g1 ^ 3 * h0 ^ 4 -
    (114850856960 : K[X]) * a5 ^ 2 * g1 ^ 5 * h0 ^ 4 -
    (162067906560 : K[X]) * b6 * a6 ^ 3 * g1 * h0 ^ 2 +
    (314006568960 : K[X]) * b6 * a6 ^ 2 * g1 ^ 3 * h0 ^ 2 -
    (153078202368 : K[X]) * b6 * a6 * g1 ^ 5 * h0 ^ 2 +
    (21412724736 : K[X]) * b6 * g1 ^ 7 * h0 ^ 2 -
    (67528294400 : K[X]) * a5 * a6 ^ 4 +
    (443154432000 : K[X]) * a5 * a6 ^ 3 * g1 ^ 2 -
    (509363814400 : K[X]) * a5 * a6 ^ 2 * g1 ^ 4 +
    (193289850880 : K[X]) * a5 * a6 * g1 ^ 6 -
    (23135424000 : K[X]) * a5 * g1 ^ 8 +
    Polynomial.C κ *
      (-(7516192768 : K[X]) * a1 * a6 * h0 ^ 22 +
        (469762048 : K[X]) * a1 * g1 ^ 2 * h0 ^ 22 -
        (7516192768 : K[X]) * a2 * a5 * h0 ^ 22 -
        (7516192768 : K[X]) * a3 * a4 * h0 ^ 22 +
        (7516192768 : K[X]) * a2 * a6 * g1 * h0 ^ 18 -
        (587202560 : K[X]) * a2 * g1 ^ 3 * h0 ^ 18 +
        (7516192768 : K[X]) * a3 * a5 * g1 * h0 ^ 18 +
        (3758096384 : K[X]) * a4 ^ 2 * g1 * h0 ^ 18 +
        (7046430720 : K[X]) * a3 * a6 ^ 2 * h0 ^ 14 -
        (7927234560 : K[X]) * a3 * a6 * g1 ^ 2 * h0 ^ 14 +
        (633077760 : K[X]) * a3 * g1 ^ 4 * h0 ^ 14 +
        (14092861440 : K[X]) * a4 * a5 * a6 * h0 ^ 14 -
        (7927234560 : K[X]) * a4 * a5 * g1 ^ 2 * h0 ^ 14 +
        (2348810240 : K[X]) * a5 ^ 3 * h0 ^ 14 -
        (14092861440 : K[X]) * a4 * a6 ^ 2 * g1 * h0 ^ 10 +
        (8441036800 : K[X]) * a4 * a6 * g1 ^ 3 * h0 ^ 10 -
        (654180352 : K[X]) * a4 * g1 ^ 5 * h0 ^ 10 -
        (14092861440 : K[X]) * a5 ^ 2 * a6 * g1 * h0 ^ 10 +
        (4220518400 : K[X]) * a5 ^ 2 * g1 ^ 3 * h0 ^ 10 -
        (6752829440 : K[X]) * a5 * a6 ^ 3 * h0 ^ 6 +
        (21524643840 : K[X]) * a5 * a6 ^ 2 * g1 ^ 2 * h0 ^ 6 -
        (8994979840 : K[X]) * a5 * a6 * g1 ^ 4 * h0 ^ 6 +
        (664401920 : K[X]) * a5 * g1 ^ 6 * h0 ^ 6 +
        (5064622080 : K[X]) * a6 ^ 4 * g1 * h0 ^ 2 -
        (9812705280 : K[X]) * a6 ^ 3 * g1 ^ 3 * h0 ^ 2 +
        (4783693824 : K[X]) * a6 ^ 2 * g1 ^ 5 * h0 ^ 2 -
        (669147648 : K[X]) * a6 * g1 ^ 7 * h0 ^ 2) -
    Polynomial.C μ *
      ((1879048192 : K[X]) * a0 * h0 ^ 29 -
        (1644167168 : K[X]) * a1 * g1 * h0 ^ 25 -
        (1644167168 : K[X]) * a2 * a6 * h0 ^ 21 +
        (1541406720 : K[X]) * a2 * g1 ^ 2 * h0 ^ 21 -
        (1644167168 : K[X]) * a3 * a5 * h0 ^ 21 -
        (822083584 : K[X]) * a4 ^ 2 * h0 ^ 21 +
        (3082813440 : K[X]) * a3 * a6 * g1 * h0 ^ 17 -
        (1477181440 : K[X]) * a3 * g1 ^ 3 * h0 ^ 17 +
        (3082813440 : K[X]) * a4 * a5 * g1 * h0 ^ 17 +
        (1541406720 : K[X]) * a4 * a6 ^ 2 * h0 ^ 13 -
        (4431544320 : K[X]) * a4 * a6 * g1 ^ 2 * h0 ^ 13 +
        (1431019520 : K[X]) * a4 * g1 ^ 4 * h0 ^ 13 +
        (1541406720 : K[X]) * a5 ^ 2 * a6 * h0 ^ 13 -
        (2215772160 : K[X]) * a5 ^ 2 * g1 ^ 2 * h0 ^ 13 -
        (4431544320 : K[X]) * a5 * a6 ^ 2 * g1 * h0 ^ 9 +
        (5724078080 : K[X]) * a5 * a6 * g1 ^ 3 * h0 ^ 9 -
        (1395244032 : K[X]) * a5 * g1 ^ 5 * h0 ^ 9 -
        (369295360 : K[X]) * a6 ^ 4 * h0 ^ 5 +
        (2862039040 : K[X]) * a6 ^ 3 * g1 ^ 2 * h0 ^ 5 -
        (3488110080 : K[X]) * a6 ^ 2 * g1 ^ 4 * h0 ^ 5 +
        (1366176448 : K[X]) * a6 * g1 ^ 6 * h0 ^ 5 -
        (167722555 : K[X]) * g1 ^ 8 * h0 ^ 5)

/-- Cleared eleventh row of the square chamber, in factored form: `h₀⁴`
times the transport co-factor minus the pure `g₁, p₆` undecic block. -/
def alignedEleventhSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedEleventhSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ μ -
    (1840 : K[X]) * g1 *
      ((662935 : K[X]) * g1 ^ 10 - (8788624 : K[X]) * a6 * g1 ^ 8 +
        (43253184 : K[X]) * a6 ^ 2 * g1 ^ 6 -
        (96216064 : K[X]) * a6 ^ 3 * g1 ^ 4 +
        (92323840 : K[X]) * a6 ^ 4 * g1 ^ 2 -
        (27525120 : K[X]) * a6 ^ 5)

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the nonsquare-chamber eleventh row
(`p₇ = H² g₂`, `H²²` peeled, `128 q₇ H` consumed): `q₁` sits at `H¹³`
here, i.e. at `H¹⁵` in the cleared row. -/
def alignedEleventhNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(300647710720 : K[X]) * a1 * a4 * H ^ 12 -
    (300647710720 : K[X]) * a2 * a3 * H ^ 12 +
    (206158430208 : K[X]) * a1 * b6 * H ^ 11 +
    (171798691840 : K[X]) * a2 * b5 * H ^ 11 +
    (137438953472 : K[X]) * a3 * b4 * H ^ 11 +
    (103079215104 : K[X]) * a4 * b3 * H ^ 11 +
    (68719476736 : K[X]) * a5 * b2 * H ^ 11 +
    (34359738368 : K[X]) * b1 * a6 * H ^ 11 -
    (15032385536 : K[X]) * b1 * g2 ^ 2 * H ^ 11 -
    (37580963840 : K[X]) * a1 * a5 * g2 * H ^ 10 +
    (225485783040 : K[X]) * a2 * a4 * g2 * H ^ 10 +
    (112742891520 : K[X]) * a3 ^ 2 * g2 * H ^ 10 -
    (180388626432 : K[X]) * a2 * b6 * g2 * H ^ 9 -
    (150323855360 : K[X]) * a3 * b5 * g2 * H ^ 9 -
    (120259084288 : K[X]) * a4 * b4 * g2 * H ^ 9 -
    (90194313216 : K[X]) * a5 * b3 * g2 * H ^ 9 -
    (60129542144 : K[X]) * b2 * a6 * g2 * H ^ 9 +
    (18790481920 : K[X]) * b2 * g2 ^ 3 * H ^ 9 -
    (18790481920 : K[X]) * a1 * a6 ^ 2 * H ^ 8 +
    (2348810240 : K[X]) * a1 * a6 * g2 ^ 2 * H ^ 8 +
    (1247805440 : K[X]) * a1 * g2 ^ 4 * H ^ 8 +
    (32883343360 : K[X]) * a2 * a5 * g2 ^ 2 * H ^ 8 +
    (263066746880 : K[X]) * a3 * a4 * a6 * H ^ 8 -
    (213741731840 : K[X]) * a3 * a4 * g2 ^ 2 * H ^ 8 +
    (18790481920 : K[X]) * a3 * a5 ^ 2 * H ^ 8 +
    (150323855360 : K[X]) * a4 ^ 2 * a5 * H ^ 8 -
    (180388626432 : K[X]) * a3 * b6 * a6 * H ^ 7 +
    (169114337280 : K[X]) * a3 * b6 * g2 ^ 2 * H ^ 7 -
    (180388626432 : K[X]) * a4 * a5 * b6 * H ^ 7 -
    (150323855360 : K[X]) * a4 * b5 * a6 * H ^ 7 +
    (140928614400 : K[X]) * a4 * b5 * g2 ^ 2 * H ^ 7 -
    (75161927680 : K[X]) * a5 ^ 2 * b5 * H ^ 7 -
    (120259084288 : K[X]) * a5 * b4 * a6 * H ^ 7 +
    (112742891520 : K[X]) * a5 * b4 * g2 ^ 2 * H ^ 7 -
    (45097156608 : K[X]) * b3 * a6 ^ 2 * H ^ 7 +
    (84557168640 : K[X]) * b3 * a6 * g2 ^ 2 * H ^ 7 -
    (20258488320 : K[X]) * b3 * g2 ^ 4 * H ^ 7 +
    (4697620480 : K[X]) * a2 * a6 ^ 2 * g2 * H ^ 6 +
    (5284823040 : K[X]) * a2 * a6 * g2 ^ 3 * H ^ 6 -
    (2220359680 : K[X]) * a2 * g2 ^ 5 * H ^ 6 +
    (4697620480 : K[X]) * a3 * a5 * a6 * g2 * H ^ 6 -
    (22607298560 : K[X]) * a3 * a5 * g2 ^ 3 * H ^ 6 -
    (244276264960 : K[X]) * a4 ^ 2 * a6 * g2 * H ^ 6 +
    (106870865920 : K[X]) * a4 ^ 2 * g2 ^ 3 * H ^ 6 +
    (338228674560 : K[X]) * a4 * b6 * a6 * g2 * H ^ 5 -
    (162067906560 : K[X]) * a4 * b6 * g2 ^ 3 * H ^ 5 +
    (169114337280 : K[X]) * a5 ^ 2 * b6 * g2 * H ^ 5 +
    (281857228800 : K[X]) * a5 * b5 * a6 * g2 * H ^ 5 -
    (135056588800 : K[X]) * a5 * b5 * g2 ^ 3 * H ^ 5 +
    (112742891520 : K[X]) * b4 * a6 ^ 2 * g2 * H ^ 5 -
    (108045271040 : K[X]) * b4 * a6 * g2 ^ 3 * H ^ 5 +
    (20933771264 : K[X]) * b4 * g2 ^ 5 * H ^ 5 +
    (11744051200 : K[X]) * a3 * a6 ^ 3 * H ^ 4 +
    (6606028800 : K[X]) * a3 * a6 ^ 2 * g2 ^ 2 * H ^ 4 -
    (12248678400 : K[X]) * a3 * a6 * g2 ^ 4 * H ^ 4 +
    (2888417280 : K[X]) * a3 * g2 ^ 6 * H ^ 4 -
    (8808038400 : K[X]) * a4 * a5 * a6 * g2 ^ 2 * H ^ 4 +
    (14129561600 : K[X]) * a4 * a5 * g2 ^ 4 * H ^ 4 +
    (70464307200 : K[X]) * a5 ^ 3 * a6 * H ^ 4 -
    (123312537600 : K[X]) * a5 ^ 3 * g2 ^ 2 * H ^ 4 +
    (169114337280 : K[X]) * a5 * b6 * a6 ^ 2 * H ^ 3 -
    (486203719680 : K[X]) * a5 * b6 * a6 * g2 ^ 2 * H ^ 3 +
    (157003284480 : K[X]) * a5 * b6 * g2 ^ 4 * H ^ 3 +
    (46976204800 : K[X]) * b5 * a6 ^ 3 * H ^ 3 -
    (202584883200 : K[X]) * b5 * a6 ^ 2 * g2 ^ 2 * H ^ 3 +
    (130836070400 : K[X]) * b5 * a6 * g2 ^ 4 * H ^ 3 -
    (21260861440 : K[X]) * b5 * g2 ^ 6 * H ^ 3 -
    (5872025600 : K[X]) * a4 * a6 ^ 3 * g2 * H ^ 2 -
    (24589107200 : K[X]) * a4 * a6 ^ 2 * g2 ^ 3 * H ^ 2 +
    (18886819840 : K[X]) * a4 * a6 * g2 ^ 5 * H ^ 2 -
    (3358515200 : K[X]) * a4 * g2 ^ 7 * H ^ 2 -
    (343513497600 : K[X]) * a5 ^ 2 * a6 ^ 2 * g2 * H ^ 2 +
    (456549990400 : K[X]) * a5 ^ 2 * a6 * g2 ^ 3 * H ^ 2 -
    (114850856960 : K[X]) * a5 ^ 2 * g2 ^ 5 * H ^ 2 -
    (162067906560 : K[X]) * b6 * a6 ^ 3 * g2 * H +
    (314006568960 : K[X]) * b6 * a6 ^ 2 * g2 ^ 3 * H -
    (153078202368 : K[X]) * b6 * a6 * g2 ^ 5 * H +
    (21412724736 : K[X]) * b6 * g2 ^ 7 * H -
    (67528294400 : K[X]) * a5 * a6 ^ 4 +
    (443154432000 : K[X]) * a5 * a6 ^ 3 * g2 ^ 2 -
    (509363814400 : K[X]) * a5 * a6 ^ 2 * g2 ^ 4 +
    (193289850880 : K[X]) * a5 * a6 * g2 ^ 6 -
    (23135424000 : K[X]) * a5 * g2 ^ 8 +
    Polynomial.C κ *
      (-(7516192768 : K[X]) * a1 * a6 * H ^ 11 +
        (469762048 : K[X]) * a1 * g2 ^ 2 * H ^ 11 -
        (7516192768 : K[X]) * a2 * a5 * H ^ 11 -
        (7516192768 : K[X]) * a3 * a4 * H ^ 11 +
        (7516192768 : K[X]) * a2 * a6 * g2 * H ^ 9 -
        (587202560 : K[X]) * a2 * g2 ^ 3 * H ^ 9 +
        (7516192768 : K[X]) * a3 * a5 * g2 * H ^ 9 +
        (3758096384 : K[X]) * a4 ^ 2 * g2 * H ^ 9 +
        (7046430720 : K[X]) * a3 * a6 ^ 2 * H ^ 7 -
        (7927234560 : K[X]) * a3 * a6 * g2 ^ 2 * H ^ 7 +
        (633077760 : K[X]) * a3 * g2 ^ 4 * H ^ 7 +
        (14092861440 : K[X]) * a4 * a5 * a6 * H ^ 7 -
        (7927234560 : K[X]) * a4 * a5 * g2 ^ 2 * H ^ 7 +
        (2348810240 : K[X]) * a5 ^ 3 * H ^ 7 -
        (14092861440 : K[X]) * a4 * a6 ^ 2 * g2 * H ^ 5 +
        (8441036800 : K[X]) * a4 * a6 * g2 ^ 3 * H ^ 5 -
        (654180352 : K[X]) * a4 * g2 ^ 5 * H ^ 5 -
        (14092861440 : K[X]) * a5 ^ 2 * a6 * g2 * H ^ 5 +
        (4220518400 : K[X]) * a5 ^ 2 * g2 ^ 3 * H ^ 5 -
        (6752829440 : K[X]) * a5 * a6 ^ 3 * H ^ 3 +
        (21524643840 : K[X]) * a5 * a6 ^ 2 * g2 ^ 2 * H ^ 3 -
        (8994979840 : K[X]) * a5 * a6 * g2 ^ 4 * H ^ 3 +
        (664401920 : K[X]) * a5 * g2 ^ 6 * H ^ 3 +
        (5064622080 : K[X]) * a6 ^ 4 * g2 * H -
        (9812705280 : K[X]) * a6 ^ 3 * g2 ^ 3 * H +
        (4783693824 : K[X]) * a6 ^ 2 * g2 ^ 5 * H -
        (669147648 : K[X]) * a6 * g2 ^ 7 * H)

/-- Cleared eleventh row of the nonsquare chamber, in factored form:
`H²` times the transport co-factor minus the pure `g₂, p₆` undecic
block. -/
def alignedEleventhNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedEleventhNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ -
    (1840 : K[X]) * g2 *
      ((662935 : K[X]) * g2 ^ 10 - (8788624 : K[X]) * a6 * g2 ^ 8 +
        (43253184 : K[X]) * a6 ^ 2 * g2 ^ 6 -
        (96216064 : K[X]) * a6 ^ 3 * g2 ^ 4 +
        (92323840 : K[X]) * a6 ^ 4 * g2 ^ 2 -
        (27525120 : K[X]) * a6 ^ 5)

/-! ## Square chamber -/

/-- In the square chamber the squared weight-seventy-seven integral has
a polynomial square root with square core: `N₁₁ = ν₄ h₀⁷⁷` with
`ν₄² = κ₁₀`.  The constant `ν₄` is preserved, not cleared. -/
theorem alignedSquareEleventh_sqrt_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₁₀ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hN2 : alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 77) :
    ∃ ν₄ : K, ν₄ ^ 2 = κ₁₀ ∧
      alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
          b6 b7 κ =
        Polynomial.C ν₄ * h0 ^ 77 := by
  set N : K[X] :=
    alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
      b6 b7 κ
    with hNdef
  have hdvd : (h0 ^ 77) ^ 2 ∣ N ^ 2 := by
    refine ⟨Polynomial.C κ₁₀, ?_⟩
    rw [hN2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ := by
    have h154 := hN2
    rw [hG, hHsq] at h154
    apply mul_left_cancel₀ (pow_ne_zero 154 hh0)
    linear_combination h154
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₁₀
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν₄, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν₄, ?_, ?_⟩
  · have hCν : Polynomial.C (ν₄ ^ 2) = Polynomial.C κ₁₀ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀⁴⁴` from `N₁₁ = ν₄ h₀⁷⁷` on `H = h₀²`, `p₇ = h₀⁴ g₁`
and consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `1879048192 p₀ h₀²⁴ - 1644167168 p₁ g₁ h₀²⁰
- 1644167168 p₂ p₆ h₀¹⁶ + 1541406720 p₂ g₁² h₀¹⁶ - 1644167168 p₃ p₅ h₀¹⁶
- 822083584 p₄² h₀¹⁶ + 3082813440 p₃ p₆ g₁ h₀¹² - 1477181440 p₃ g₁³ h₀¹²
+ 3082813440 p₄ p₅ g₁ h₀¹² + 1541406720 p₄ p₆² h₀⁸
- 4431544320 p₄ p₆ g₁² h₀⁸ + 1431019520 p₄ g₁⁴ h₀⁸ + 1541406720 p₅² p₆ h₀⁸
- 2215772160 p₅² g₁² h₀⁸ - 4431544320 p₅ p₆² g₁ h₀⁴
+ 5724078080 p₅ p₆ g₁³ h₀⁴ - 1395244032 p₅ g₁⁵ h₀⁴ - 369295360 p₆⁴
+ 2862039040 p₆³ g₁² - 3488110080 p₆² g₁⁴ + 1366176448 p₆ g₁⁶
- 167722555 g₁⁸`, leaves the cleared eleventh row of the square chamber
together with its factored transport form. -/
theorem alignedSquareEleventh_solved_810 {K : Type*} [Field K]
    [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ ν₄ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hN : alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C ν₄ * h0 ^ 77)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedEleventhSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
        b5 b6 κ μ =
      Polynomial.C ν₄ * h0 ^ 33 ∧
    (1840 : K[X]) * g1 *
        ((662935 : K[X]) * g1 ^ 10 - (8788624 : K[X]) * a6 * g1 ^ 8 +
          (43253184 : K[X]) * a6 ^ 2 * g1 ^ 6 -
          (96216064 : K[X]) * a6 ^ 3 * g1 ^ 4 +
          (92323840 : K[X]) * a6 ^ 4 * g1 ^ 2 -
          (27525120 : K[X]) * a6 ^ 5) =
      h0 ^ 4 *
        (alignedEleventhSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2
            b3 b4 b5 b6 κ μ -
          Polynomial.C ν₄ * h0 ^ 29) := by
  have hN' := hN
  simp only [alignedEleventhDefect810, hHsq, hg] at hN'
  have hclear :
      alignedEleventhSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ μ =
        Polynomial.C ν₄ * h0 ^ 33 := by
    simp only [alignedEleventhSquareRow810, alignedEleventhSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 44 hh0)
    linear_combination hN' -
      h0 ^ 44 *
        ((1879048192 : K[X]) * a0 * h0 ^ 24 -
          (1644167168 : K[X]) * a1 * g1 * h0 ^ 20 -
          (1644167168 : K[X]) * a2 * a6 * h0 ^ 16 +
          (1541406720 : K[X]) * a2 * g1 ^ 2 * h0 ^ 16 -
          (1644167168 : K[X]) * a3 * a5 * h0 ^ 16 -
          (822083584 : K[X]) * a4 ^ 2 * h0 ^ 16 +
          (3082813440 : K[X]) * a3 * a6 * g1 * h0 ^ 12 -
          (1477181440 : K[X]) * a3 * g1 ^ 3 * h0 ^ 12 +
          (3082813440 : K[X]) * a4 * a5 * g1 * h0 ^ 12 +
          (1541406720 : K[X]) * a4 * a6 ^ 2 * h0 ^ 8 -
          (4431544320 : K[X]) * a4 * a6 * g1 ^ 2 * h0 ^ 8 +
          (1431019520 : K[X]) * a4 * g1 ^ 4 * h0 ^ 8 +
          (1541406720 : K[X]) * a5 ^ 2 * a6 * h0 ^ 8 -
          (2215772160 : K[X]) * a5 ^ 2 * g1 ^ 2 * h0 ^ 8 -
          (4431544320 : K[X]) * a5 * a6 ^ 2 * g1 * h0 ^ 4 +
          (5724078080 : K[X]) * a5 * a6 * g1 ^ 3 * h0 ^ 4 -
          (1395244032 : K[X]) * a5 * g1 ^ 5 * h0 ^ 4 -
          (369295360 : K[X]) * a6 ^ 4 +
          (2862039040 : K[X]) * a6 ^ 3 * g1 ^ 2 -
          (3488110080 : K[X]) * a6 ^ 2 * g1 ^ 4 +
          (1366176448 : K[X]) * a6 * g1 ^ 6 -
          (167722555 : K[X]) * g1 ^ 8) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedEleventhSquareRow810] at hclear
  linear_combination -hclear

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the squared
weight-seventy-seven integral forces its constant to vanish, and with
it the whole eleventh defect. -/
theorem alignedNonsquareEleventh_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : k[X]} {κ κ₁₀ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hN2 : alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 77) :
    κ₁₀ = 0 ∧
      alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
          b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set N : k[X] :=
    alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
      b6 b7 κ
    with hNdef
  have hdvd : (H ^ 38) ^ 2 ∣ N ^ 2 := by
    refine ⟨Polynomial.C κ₁₀ * H, ?_⟩
    rw [hN2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 76 hH)
    have h76 := hN2
    rw [hG] at h76
    linear_combination h76
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₁₀ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk10 : κ₁₀ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hNzero : N = 0 := by
    have hsq : N ^ 2 = 0 := by
      rw [hN2, hk10]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk10, hNzero⟩

set_option maxHeartbeats 1600000000 in
/-- Peeling `H²²` from the vanished eleventh defect on `p₇ = H² g₂`,
then consuming the previous factored quotient with the mate
`1879048192 p₀ H¹² - 1644167168 p₁ g₂ H¹⁰ - 1644167168 p₂ p₆ H⁸
+ 1541406720 p₂ g₂² H⁸ - 1644167168 p₃ p₅ H⁸ - 822083584 p₄² H⁸
+ 3082813440 p₃ p₆ g₂ H⁶ - 1477181440 p₃ g₂³ H⁶ + 3082813440 p₄ p₅ g₂ H⁶
+ 1541406720 p₄ p₆² H⁴ - 4431544320 p₄ p₆ g₂² H⁴ + 1431019520 p₄ g₂⁴ H⁴
+ 1541406720 p₅² p₆ H⁴ - 2215772160 p₅² g₂² H⁴ - 4431544320 p₅ p₆² g₂ H²
+ 5724078080 p₅ p₆ g₂³ H² - 1395244032 p₅ g₂⁵ H² - 369295360 p₆⁴
+ 2862039040 p₆³ g₂² - 3488110080 p₆² g₂⁴ + 1366176448 p₆ g₂⁶
- 167722555 g₂⁸`, leaves the cleared eleventh row of the nonsquare
chamber together with its factored transport form. -/
theorem alignedNonsquareEleventh_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hN0 : alignedEleventhDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3
        b4 b5 b6 b7 κ = 0)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedEleventhNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
        b4 b5 b6 κ = 0 ∧
    (1840 : K[X]) * g2 *
        ((662935 : K[X]) * g2 ^ 10 - (8788624 : K[X]) * a6 * g2 ^ 8 +
          (43253184 : K[X]) * a6 ^ 2 * g2 ^ 6 -
          (96216064 : K[X]) * a6 ^ 3 * g2 ^ 4 +
          (92323840 : K[X]) * a6 ^ 4 * g2 ^ 2 -
          (27525120 : K[X]) * a6 ^ 5) =
      H ^ 2 *
        alignedEleventhNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2
          b3 b4 b5 b6 κ := by
  have hN' := hN0
  simp only [alignedEleventhDefect810, hg2] at hN'
  have hclear :
      alignedEleventhNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b1 b2 b3
          b4 b5 b6 κ = 0 := by
    simp only [alignedEleventhNonsquareRow810,
      alignedEleventhNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 22 hH)
    rw [mul_zero]
    linear_combination hN' -
      H ^ 22 *
        ((1879048192 : K[X]) * a0 * H ^ 12 -
          (1644167168 : K[X]) * a1 * g2 * H ^ 10 -
          (1644167168 : K[X]) * a2 * a6 * H ^ 8 +
          (1541406720 : K[X]) * a2 * g2 ^ 2 * H ^ 8 -
          (1644167168 : K[X]) * a3 * a5 * H ^ 8 -
          (822083584 : K[X]) * a4 ^ 2 * H ^ 8 +
          (3082813440 : K[X]) * a3 * a6 * g2 * H ^ 6 -
          (1477181440 : K[X]) * a3 * g2 ^ 3 * H ^ 6 +
          (3082813440 : K[X]) * a4 * a5 * g2 * H ^ 6 +
          (1541406720 : K[X]) * a4 * a6 ^ 2 * H ^ 4 -
          (4431544320 : K[X]) * a4 * a6 * g2 ^ 2 * H ^ 4 +
          (1431019520 : K[X]) * a4 * g2 ^ 4 * H ^ 4 +
          (1541406720 : K[X]) * a5 ^ 2 * a6 * H ^ 4 -
          (2215772160 : K[X]) * a5 ^ 2 * g2 ^ 2 * H ^ 4 -
          (4431544320 : K[X]) * a5 * a6 ^ 2 * g2 * H ^ 2 +
          (5724078080 : K[X]) * a5 * a6 * g2 ^ 3 * H ^ 2 -
          (1395244032 : K[X]) * a5 * g2 ^ 5 * H ^ 2 -
          (369295360 : K[X]) * a6 ^ 4 +
          (2862039040 : K[X]) * a6 ^ 3 * g2 ^ 2 -
          (3488110080 : K[X]) * a6 ^ 2 * g2 ^ 4 +
          (1366176448 : K[X]) * a6 * g2 ^ 6 -
          (167722555 : K[X]) * g2 ^ 8) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedEleventhNonsquareRow810] at hclear
  linear_combination -hclear

/-! ## Source-facing eleventh-row packets -/

/-- Source-facing squared weight-seventy-seven integral of a normalized
aligned scale-two `(8,10)` source: the degree-`6` row is consumed into
`N₁₁² = κ₁₀ H⁷⁷` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedEleventhFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ : K),
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
          Polynomial.C κ₁₀ * H ^ 77 := by
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
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀,
    aligned_q9_solved_810 haligned, hM, hE4, hF2, hG, hI2, hJ, hL2,
    hN10, hN11⟩

/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`6`
row gives `N₁₁ = ν₄ h₀⁷⁷` with `ν₄² = κ₁₀`, the cleared eleventh row
against `ν₄ h₀³³`, the carried root collapse `g₁ = p₆ = 0`, and the
carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedEleventhFace_squareChamber_packet
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
    ∃ (κ μ κ₁₀ ν₄ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ν₄ ^ 2 = κ₁₀ ∧
        alignedEleventhSquareRow810 h0 g1 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ μ =
          Polynomial.C ν₄ * h0 ^ 33 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₄ * h0 ^ 77 := by
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
  obtain ⟨κ₁₀, hN2⟩ :=
    alignedEleventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨ν₄, hν4, hN⟩ := alignedSquareEleventh_sqrt_810 hh0 hHsq hN2
  obtain ⟨hsolved11, _hfact11⟩ :=
    alignedSquareEleventh_solved_810 hh0 hHsq hp7 hN hcore
  exact ⟨κ, μ, κ₁₀, ν₄, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hν4,
    hsolved11, hcollapse, hdvdg1, hdvdp6, hN⟩

/-- Exact nonsquare-chamber eleventh packet of a normalized aligned
scale-two `(8,10)` source: the squared weight-seventy-seven constant
vanishes, the eleventh defect is identically zero, and on top of
`p₇ = H² g₂` and the previous packet the consumed degree-`6` row gives
the cleared eleventh row equal to zero, the carried root collapse
`g₂ = p₆ = 0` at every (simple) root of the core, and the carried
descents `H ∣ g₂`, `H ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
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
        alignedEleventhNonsquareRow810 H g2 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) κ = 0 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedEleventhDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = 0 := by
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
  obtain ⟨κ₁₀, hN2⟩ :=
    alignedEleventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk10, hN0⟩ :=
    alignedNonsquareEleventh_defect_eq_zero_810 hH hHdegree hnsq hN2
  obtain ⟨hclear11, _hfact11⟩ :=
    alignedNonsquareEleventh_solved_810 hH hg2 hN0 hfac
  exact ⟨κ, g2, hg2, by rw [hq9, hg2]; ring, hclear11,
    hcollapse, hdvdg2, hdvdp6, hN0⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`6`
aligned row, carrying the factored transport of the undecic block.
Neither chamber is excluded; in the square chamber `ν₄` is preserved,
in the nonsquare chamber the odd exponent forces the cleared row to
vanish.  No closure is claimed. -/
theorem normalized810ScaleTwo_alignedEleventhFace_chamberDichotomy
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
      ∃ (κ μ ν₄ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (1840 : K[X]) * g1 *
              ((662935 : K[X]) * g1 ^ 10 -
                (8788624 : K[X]) * p.coeff 6 * g1 ^ 8 +
                (43253184 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 6 -
                (96216064 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 4 +
                (92323840 : K[X]) * p.coeff 6 ^ 4 * g1 ^ 2 -
                (27525120 : K[X]) * p.coeff 6 ^ 5) =
            h0 ^ 4 *
              (alignedEleventhSquareCof810 h0 g1 (p.coeff 0) (p.coeff 1)
                  (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
                  (p.coeff 6) (q.coeff 1) (q.coeff 2) (q.coeff 3)
                  (q.coeff 4) (q.coeff 5) (q.coeff 6) κ μ -
                Polynomial.C ν₄ * h0 ^ 29) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (1840 : K[X]) * g2 *
              ((662935 : K[X]) * g2 ^ 10 -
                (8788624 : K[X]) * p.coeff 6 * g2 ^ 8 +
                (43253184 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 6 -
                (96216064 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 4 +
                (92323840 : K[X]) * p.coeff 6 ^ 4 * g2 ^ 2 -
                (27525120 : K[X]) * p.coeff 6 ^ 5) =
            H ^ 2 *
              alignedEleventhNonsquareCof810 H g2 (p.coeff 0)
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
      normalized810ScaleTwo_alignedEleventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₁₀, ν₄, g1, hp7, hq9, _hν4, hsolved11,
      hcollapse, hdvdg1, hdvdp6, _hN⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, ν₄, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedEleventhSquareRow810] at hsolved11
    linear_combination -hsolved11
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, hclear11, hcollapse,
      hdvdg2, hdvdp6, _hN0⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedEleventhNonsquareRow810] at hclear11
    linear_combination -hclear11

/-- Chamber-independent root jet after the consumed degree-`6` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its undecic content is absorbed by the
degree-`13` collapse (`alignedEleventh_rootUndecic_absorbed_810`) —
and no new coefficient occurs, so the row re-ties `q₁, …, q₇` into the
cleared eleventh row instead of killing anything new at the root. -/
theorem normalized810ScaleTwo_alignedEleventhFace_rootJet
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
  normalized810ScaleTwo_alignedTenthFace_rootJet hsource haligned

#print axioms alignedEleventhCoefficientJacobianRow_810
#print axioms alignedEleventhDefect_weightedDerivative_identity_810
#print axioms alignedEleventhDefectRow_eq_zero_810
#print axioms alignedEleventhDefectPowerRelation_810
#print axioms alignedEleventh_factored_rootBranch_810
#print axioms alignedEleventh_rootUndecic_absorbed_810
#print axioms alignedSquareEleventh_sqrt_810
#print axioms alignedSquareEleventh_solved_810
#print axioms alignedNonsquareEleventh_defect_eq_zero_810
#print axioms alignedNonsquareEleventh_solved_810
#print axioms normalized810ScaleTwo_alignedEleventhFace_packet
#print axioms normalized810ScaleTwo_alignedEleventhFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedEleventhFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedEleventhFace_rootJet

end Max11DegreeRoutes
