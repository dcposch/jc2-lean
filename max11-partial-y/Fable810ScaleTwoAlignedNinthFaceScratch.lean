import Fable810ScaleTwoAlignedEighthFaceScratch

/-! # Ninth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedEighthFaceScratch` consumed the degree-`8`
aligned Keller row (the chambered `L² = κ₈ H⁶³`).  This file consumes
the next unused aligned row, the degree-`7` Jacobian coefficient — the
first row that sees `q₀` (internal names `alignedTenth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9`/`8` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, `H G' - 21 G H' = 0`,
`2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`, `2 H L' - 63 L H' = 0`,
the degree-`7` row is the weighted derivative of the weight-seventy
defect

`N₁₀ = -1073741824 q₀ H³⁵ - 1342177280 p₁ p₅ H³² - 1342177280 p₂ p₄ H³²
  - 671088640 p₃² H³² + 939524096 p₁ q₇ H³¹ + 805306368 p₂ q₆ H³¹
  + 671088640 p₃ q₅ H³¹ + 536870912 p₄ q₄ H³¹ + 402653184 p₅ q₃ H³¹
  + 268435456 p₆ q₂ H³¹ + 134217728 p₇ q₁ H³¹ + … + 12582912 p₇¹⁰
  + κ (33554432 p₀ H³⁵ - 33554432 p₁ p₇ H³¹ - … - 4194304 p₇⁸ H⁷)`

(the full one-hundred-twelve-term expression is the literal body of
`alignedTenthDefect810`; the only new coefficient is `q₀`, entering at
`H³⁵`, and the plain block sees no `p₀` monomial — `p₀` couples only
through the `κ`-block term `33554432 κ p₀ H³⁵`), via the exact
multiplier identity

`134217728 H³² · row₇[p₈ = H⁴] = (H N₁₀' - 35 N₁₀ H')
  + 33554432 H²⁹ p₀' C
  + (4194304 p₁ H²⁴ + 3670016 p₂ p₇ H²⁰ + 3670016 p₃ p₆ H²⁰
     + 3670016 p₄ p₅ H²⁰ - 229376 p₃ p₇² H¹⁶ - 458752 p₄ p₆ p₇ H¹⁶
     - 229376 p₅² p₇ H¹⁶ - 229376 p₅ p₆² H¹⁶ + 86016 p₄ p₇³ H¹²
     + 258048 p₅ p₆ p₇² H¹² + 86016 p₆³ p₇ H¹² - 45696 p₅ p₇⁴ H⁸
     - 91392 p₆² p₇³ H⁸ + 28560 p₆ p₇⁵ H⁴ - 2805 p₇⁷) (2 H D' - 21 D H')
  + (524288 p₂ H²⁰ + 393216 p₃ p₇ H¹⁶ + 393216 p₄ p₆ H¹⁶
     + 196608 p₅² H¹⁶ - 49152 p₄ p₇² H¹² - 98304 p₅ p₆ p₇ H¹²
     - 16384 p₆³ H¹² + 20480 p₅ p₇³ H⁸ + 30720 p₆² p₇² H⁸
     - 11520 p₆ p₇⁴ H⁴ + 1248 p₇⁶) (H E' - 14 E H')
  + (32768 p₃ H¹⁶ + 20480 p₄ p₇ H¹² + 20480 p₅ p₆ H¹²
     - 3840 p₅ p₇² H⁸ - 3840 p₆² p₇ H⁸ + 1760 p₆ p₇³ H⁴
     - 209 p₇⁵) (2 H F' - 35 F H')
  + (16384 p₄ H¹² + 8192 p₅ p₇ H⁸ + 4096 p₆² H⁸ - 2048 p₆ p₇² H⁴
     + 256 p₇⁴) (H G' - 21 G H')
  + (128 p₅ H⁸ + 48 p₆ p₇ H⁴ - 5 p₇³) (2 H I' - 49 I H')
  + (32 p₆ H⁴ + 4 p₇²) (H J' - 28 J H')
  + p₇ (2 H L' - 63 L H')`.

The row never sees `q₉`, so — unlike every previous aligned row — no
`N`-correction occurs at all, and the single `C`-correction rides on
`p₀'` with no `C'` term.  On the aligned face every right-hand
correction vanishes, so `H N₁₀' = 35 N₁₀ H'` and the weight-seventy
first integral

`N₁₀ = κ₉ H³⁵`

holds for a preserved constant `κ₉`.  The defect is unsquared, so —
exactly as for the degree-`13`, degree-`11`, and degree-`9` rows — the
integral is **chamber-free**: neither chamber forces anything, and
`κ₉` is preserved in both.

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: peeling `h₀⁴⁰` and consuming
  the previous factored quotient (`128 q₇ h₀²` solved, transported by
  the mate `7340032 p₁ h₀²⁰ - 7340032 p₂ g₁ h₀¹⁶ - 7340032 p₃ p₆ h₀¹²
  + 7340032 p₃ g₁² h₀¹² - 7340032 p₄ p₅ h₀¹² + 14680064 p₄ p₆ g₁ h₀⁸
  - 7340032 p₄ g₁³ h₀⁸ + 7340032 p₅² g₁ h₀⁸ + 7340032 p₅ p₆² h₀⁴
  - 22020096 p₅ p₆ g₁² h₀⁴ + 7340032 p₅ g₁⁴ h₀⁴ - 7340032 p₆³ g₁
  + 14680064 p₆² g₁³ - 7340032 p₆ g₁⁵ + 1048576 g₁⁷`) leaves the
  cleared tenth row `alignedTenthSquareRow810` (with the new `q₀` at
  `h₀³⁰`) against `κ₉ h₀³⁰`, and the factored transport
  `1048576 (7 g₁¹⁰ - 85 p₆ g₁⁸ + 370 p₆² g₁⁶ - 685 p₆³ g₁⁴
   + 480 p₆⁴ g₁² - 64 p₆⁵) = h₀⁴ (κ₉ h₀²⁶ - co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): with
  `p₇ = H² g₂`, peeling `H²⁰` and consuming the previous factored
  quotient (same mate) leaves the cleared tenth row
  `alignedTenthNonsquareRow810` (with `q₀` at `H¹⁵`) against `κ₉ H¹⁵`
  and the transport `1048576 (7 g₂¹⁰ - 85 p₆ g₂⁸ + 370 p₆² g₂⁶
  - 685 p₆³ g₂⁴ + 480 p₆⁴ g₂² - 64 p₆⁵) = H² (κ₉ H¹³ - co-factor)`.

At a root of the transport co-factor the honest root branch is the
root decic `7 g¹⁰ - 85 p₆ g⁸ + 370 p₆² g⁶ - 685 p₆³ g⁴ + 480 p₆⁴ g²
- 64 p₆⁵ = 0` — no `g`-factor splits off, since the block is even in
`g` with a pure `p₆⁵` tail.  Like the quartic, quintic, sextic,
septic, octic, and nonic of the previous rows it adds *no new* root
information: the consumed degree-`13` row already collapsed
`g(a) = 0 ∧ p₆(a) = 0` at every core root, and that collapse absorbs
the decic identically (`alignedTenth_rootDecic_absorbed_810`).  The
chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` — the
row ties the new coefficient `q₀` into the cleared tenth row (at
`h₀³⁰`, resp. `H¹⁵`) instead of killing anything new at the root.

No closure is claimed.  Both chambers remain open, the constants `κ`,
`μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆`, `κ₇`, `κ₈`, and the new `κ₉` are
preserved where not previously forced (`κ₈ = 0` remains forced in the
nonsquare chamber only, by the consumed degree-`8` row), the zero
branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `κ₄ = 0`,
`κ₅ = 0`, `κ₆ = 0`, `κ₇ = 0`, `κ₈ = 0`, `κ₉ = 0`) are not excluded as
polynomial identities, the deepened quotients `g₁/h₀`, `p₆/h₀`,
`g₂/H`, `p₆/H` from the degree-`13` face are still not re-cleared
through the tower here, the root decic is recorded but not excluded as
an identity, and no individual vanishing of `p₀`, `p₁`, `p₂`, `p₃`,
`p₄`, `p₅`, `q₀`, `q₁`, `q₂`, `q₃`, `q₄`, `q₅`, `q₆`, `q₇` is claimed.
The next unused Keller row on the aligned face is the degree-`6`
Jacobian coefficient — the first aligned row that sees *no* new
coefficient (every `pᵢ` and `qⱼ` has now been seen; weight-seventy-
seven defect, odd exponent, hence chambered).  No total-degree or
twice-prime theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal degree-`7` Keller coefficient on the aligned face -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`7` Jacobian coefficient, the first
aligned row that sees `q₀`. -/
theorem alignedTenthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 7) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (7 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 7 :
      Finset (ℕ × ℕ)) =
      ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1),
        (7, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8]
  linear_combination hcoeff

/-! ## Aligned tenth defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-seventy defect of the degree-`7` aligned `(8,10)` row.  On
the aligned face it is a polynomial first integral of even weight
seventy, hence chamber-free.  The only new coefficient is `q₀`; the
plain block sees no `p₀` monomial (`p₀` couples only through the
`κ`-block). -/
def alignedTenthDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X])
    (κ : K) :
    K[X] :=
    -(1073741824 : K[X]) * b0 * H ^ 35 -
    (1342177280 : K[X]) * a1 * a5 * H ^ 32 -
    (1342177280 : K[X]) * a2 * a4 * H ^ 32 -
    (671088640 : K[X]) * a3 ^ 2 * H ^ 32 +
    (939524096 : K[X]) * a1 * b7 * H ^ 31 +
    (805306368 : K[X]) * a2 * b6 * H ^ 31 +
    (671088640 : K[X]) * a3 * b5 * H ^ 31 +
    (536870912 : K[X]) * a4 * b4 * H ^ 31 +
    (402653184 : K[X]) * a5 * b3 * H ^ 31 +
    (268435456 : K[X]) * b2 * a6 * H ^ 31 +
    (134217728 : K[X]) * b1 * a7 * H ^ 31 -
    (167772160 : K[X]) * a1 * a6 * a7 * H ^ 28 +
    (1174405120 : K[X]) * a2 * a5 * a7 * H ^ 28 +
    (1174405120 : K[X]) * a3 * a4 * a7 * H ^ 28 +
    (1342177280 : K[X]) * a3 * a5 * a6 * H ^ 28 +
    (671088640 : K[X]) * a4 ^ 2 * a6 * H ^ 28 +
    (1342177280 : K[X]) * a4 * a5 ^ 2 * H ^ 28 -
    (939524096 : K[X]) * a2 * b7 * a7 * H ^ 27 -
    (939524096 : K[X]) * a3 * b7 * a6 * H ^ 27 -
    (805306368 : K[X]) * a3 * b6 * a7 * H ^ 27 -
    (939524096 : K[X]) * a4 * a5 * b7 * H ^ 27 -
    (805306368 : K[X]) * a4 * b6 * a6 * H ^ 27 -
    (671088640 : K[X]) * a4 * b5 * a7 * H ^ 27 -
    (402653184 : K[X]) * a5 ^ 2 * b6 * H ^ 27 -
    (671088640 : K[X]) * a5 * b5 * a6 * H ^ 27 -
    (536870912 : K[X]) * a5 * b4 * a7 * H ^ 27 -
    (268435456 : K[X]) * b4 * a6 ^ 2 * H ^ 27 -
    (402653184 : K[X]) * b3 * a6 * a7 * H ^ 27 -
    (134217728 : K[X]) * b2 * a7 ^ 2 * H ^ 27 +
    (167772160 : K[X]) * a2 * a6 * a7 ^ 2 * H ^ 24 -
    (1174405120 : K[X]) * a3 * a5 * a7 ^ 2 * H ^ 24 +
    (167772160 : K[X]) * a3 * a6 ^ 2 * a7 * H ^ 24 -
    (587202560 : K[X]) * a4 ^ 2 * a7 ^ 2 * H ^ 24 -
    (2348810240 : K[X]) * a4 * a5 * a6 * a7 * H ^ 24 -
    (838860800 : K[X]) * a5 ^ 3 * a7 * H ^ 24 -
    (671088640 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 24 +
    (939524096 : K[X]) * a3 * b7 * a7 ^ 2 * H ^ 23 +
    (1879048192 : K[X]) * a4 * b7 * a6 * a7 * H ^ 23 +
    (805306368 : K[X]) * a4 * b6 * a7 ^ 2 * H ^ 23 +
    (939524096 : K[X]) * a5 ^ 2 * b7 * a7 * H ^ 23 +
    (939524096 : K[X]) * a5 * b7 * a6 ^ 2 * H ^ 23 +
    (1610612736 : K[X]) * a5 * b6 * a6 * a7 * H ^ 23 +
    (671088640 : K[X]) * a5 * b5 * a7 ^ 2 * H ^ 23 +
    (268435456 : K[X]) * b6 * a6 ^ 3 * H ^ 23 +
    (671088640 : K[X]) * b5 * a6 ^ 2 * a7 * H ^ 23 +
    (536870912 : K[X]) * b4 * a6 * a7 ^ 2 * H ^ 23 +
    (134217728 : K[X]) * b3 * a7 ^ 3 * H ^ 23 -
    (167772160 : K[X]) * a3 * a6 * a7 ^ 3 * H ^ 20 +
    (1174405120 : K[X]) * a4 * a5 * a7 ^ 3 * H ^ 20 -
    (335544320 : K[X]) * a4 * a6 ^ 2 * a7 ^ 2 * H ^ 20 +
    (1677721600 : K[X]) * a5 ^ 2 * a6 * a7 ^ 2 * H ^ 20 -
    (167772160 : K[X]) * a5 * a6 ^ 3 * a7 * H ^ 20 -
    (67108864 : K[X]) * a6 ^ 5 * H ^ 20 -
    (939524096 : K[X]) * a4 * b7 * a7 ^ 3 * H ^ 19 -
    (2818572288 : K[X]) * a5 * b7 * a6 * a7 ^ 2 * H ^ 19 -
    (805306368 : K[X]) * a5 * b6 * a7 ^ 3 * H ^ 19 -
    (939524096 : K[X]) * b7 * a6 ^ 3 * a7 * H ^ 19 -
    (1207959552 : K[X]) * b6 * a6 ^ 2 * a7 ^ 2 * H ^ 19 -
    (671088640 : K[X]) * b5 * a6 * a7 ^ 3 * H ^ 19 -
    (134217728 : K[X]) * b4 * a7 ^ 4 * H ^ 19 +
    (167772160 : K[X]) * a4 * a6 * a7 ^ 4 * H ^ 16 -
    (587202560 : K[X]) * a5 ^ 2 * a7 ^ 4 * H ^ 16 +
    (503316480 : K[X]) * a5 * a6 ^ 2 * a7 ^ 3 * H ^ 16 +
    (796917760 : K[X]) * a6 ^ 4 * a7 ^ 2 * H ^ 16 +
    (939524096 : K[X]) * a5 * b7 * a7 ^ 4 * H ^ 15 +
    (1879048192 : K[X]) * b7 * a6 ^ 2 * a7 ^ 3 * H ^ 15 +
    (805306368 : K[X]) * b6 * a6 * a7 ^ 4 * H ^ 15 +
    (134217728 : K[X]) * b5 * a7 ^ 5 * H ^ 15 -
    (167772160 : K[X]) * a5 * a6 * a7 ^ 5 * H ^ 12 -
    (1342177280 : K[X]) * a6 ^ 3 * a7 ^ 4 * H ^ 12 -
    (939524096 : K[X]) * b7 * a6 * a7 ^ 5 * H ^ 11 -
    (134217728 : K[X]) * b6 * a7 ^ 6 * H ^ 11 +
    (754974720 : K[X]) * a6 ^ 2 * a7 ^ 6 * H ^ 8 +
    (134217728 : K[X]) * b7 * a7 ^ 7 * H ^ 7 -
    (167772160 : K[X]) * a6 * a7 ^ 8 * H ^ 4 +
    (12582912 : K[X]) * a7 ^ 10 +
    Polynomial.C κ *
      ((33554432 : K[X]) * a0 * H ^ 35 -
        (33554432 : K[X]) * a1 * a7 * H ^ 31 -
        (33554432 : K[X]) * a2 * a6 * H ^ 31 -
        (33554432 : K[X]) * a3 * a5 * H ^ 31 -
        (16777216 : K[X]) * a4 ^ 2 * H ^ 31 +
        (33554432 : K[X]) * a2 * a7 ^ 2 * H ^ 27 +
        (67108864 : K[X]) * a3 * a6 * a7 * H ^ 27 +
        (67108864 : K[X]) * a4 * a5 * a7 * H ^ 27 +
        (33554432 : K[X]) * a4 * a6 ^ 2 * H ^ 27 +
        (33554432 : K[X]) * a5 ^ 2 * a6 * H ^ 27 -
        (33554432 : K[X]) * a3 * a7 ^ 3 * H ^ 23 -
        (100663296 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 23 -
        (50331648 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 23 -
        (100663296 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 23 -
        (8388608 : K[X]) * a6 ^ 4 * H ^ 23 +
        (33554432 : K[X]) * a4 * a7 ^ 4 * H ^ 19 +
        (134217728 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 19 +
        (67108864 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 19 -
        (33554432 : K[X]) * a5 * a7 ^ 5 * H ^ 15 -
        (83886080 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 15 +
        (33554432 : K[X]) * a6 * a7 ^ 6 * H ^ 11 -
        (4194304 : K[X]) * a7 ^ 8 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`7` Jacobian expression with the
weighted derivative of `N₁₀`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, degree-`12`, degree-`11`, degree-`10`,
degree-`9`, and degree-`8` rows.  The row never sees `q₉`, so no
`N`-correction occurs; the single `C`-correction rides on `p₀'`. -/
theorem alignedTenthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 b8 : K[X])
    (κ : K) :
    (134217728 : K[X]) * H ^ 32 *
        (a7.derivative * b1 +
          a6.derivative * (b2 * (2 : K[X])) +
          a5.derivative * (b3 * (3 : K[X])) +
          a4.derivative * (b4 * (4 : K[X])) +
          a3.derivative * (b5 * (5 : K[X])) +
          a2.derivative * (b6 * (6 : K[X])) +
          a1.derivative * (b7 * (7 : K[X])) +
          a0.derivative * (b8 * (8 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b0.derivative +
          (a7 * (7 : K[X])) * b1.derivative +
          (a6 * (6 : K[X])) * b2.derivative +
          (a5 * (5 : K[X])) * b3.derivative +
          (a4 * (4 : K[X])) * b4.derivative +
          (a3 * (3 : K[X])) * b5.derivative +
          (a2 * (2 : K[X])) * b6.derivative +
          a1 * b7.derivative)) =
      (H *
          (alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3
            b4 b5 b6 b7 κ).derivative -
        (35 : K[X]) *
          alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3
            b4 b5 b6 b7 κ * H.derivative) +
        (33554432 : K[X]) * H ^ 29 * a0.derivative *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) +
        ((4194304 : K[X]) * a1 * H ^ 24 +
            (3670016 : K[X]) * a2 * a7 * H ^ 20 +
            (3670016 : K[X]) * a3 * a6 * H ^ 20 +
            (3670016 : K[X]) * a4 * a5 * H ^ 20 -
            (229376 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
            (458752 : K[X]) * a4 * a6 * a7 * H ^ 16 -
            (229376 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
            (229376 : K[X]) * a5 * a6 ^ 2 * H ^ 16 +
            (86016 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
            (258048 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
            (86016 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
            (45696 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
            (91392 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
            (28560 : K[X]) * a6 * a7 ^ 5 * H ^ 4 -
            (2805 : K[X]) * a7 ^ 7) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((524288 : K[X]) * a2 * H ^ 20 +
            (393216 : K[X]) * a3 * a7 * H ^ 16 +
            (393216 : K[X]) * a4 * a6 * H ^ 16 +
            (196608 : K[X]) * a5 ^ 2 * H ^ 16 -
            (49152 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (98304 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (16384 : K[X]) * a6 ^ 3 * H ^ 12 +
            (20480 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (30720 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (11520 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (1248 : K[X]) * a7 ^ 6) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((32768 : K[X]) * a3 * H ^ 16 +
            (20480 : K[X]) * a4 * a7 * H ^ 12 +
            (20480 : K[X]) * a5 * a6 * H ^ 12 -
            (3840 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (3840 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (1760 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (209 : K[X]) * a7 ^ 5) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((16384 : K[X]) * a4 * H ^ 12 + (8192 : K[X]) * a5 * a7 * H ^ 8 +
            (4096 : K[X]) * a6 ^ 2 * H ^ 8 -
            (2048 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (256 : K[X]) * a7 ^ 4) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((128 : K[X]) * a5 * H ^ 8 + (48 : K[X]) * a6 * a7 * H ^ 4 -
            (5 : K[X]) * a7 ^ 3) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        ((32 : K[X]) * a6 * H ^ 4 + (4 : K[X]) * a7 ^ 2) *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) +
        a7 *
          ((2 : K[X]) * H *
              (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ).derivative -
            (63 : K[X]) *
              alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4
                b5 b6 b7 κ * H.derivative) := by
  simp only [alignedTenthDefect810, alignedNinthDefect810,
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
degree-`8` rows, the degree-`7` row is the weighted derivative
`H N₁₀' - 35 N₁₀ H' = 0`. -/
theorem alignedTenthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H *
        (alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (35 : K[X]) *
        alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedTenthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8] at hrow
  have hC0 :
      (32 : K[X]) * q.coeff 8 * H ^ 3 - (40 : K[X]) * p.coeff 6 * H ^ 4 -
          (5 : K[X]) * p.coeff 7 ^ 2 - Polynomial.C κ * H ^ 7 = 0 := by
    have hM' :
        (32 : K[X]) * q.coeff 8 * H ^ 3 -
            (40 : K[X]) * p.coeff 6 * H ^ 4 -
            (5 : K[X]) * p.coeff 7 ^ 2 = Polynomial.C κ * H ^ 7 := by
      simpa only [alignedSecondDefect810] using hM
    linear_combination hM'
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
  have hid := alignedTenthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 0) (q.coeff 1)
    (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) (q.coeff 8) κ
  rw [hrow, hC0, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ, hrowL]
    at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-seventy polynomial first integral of the aligned `(8,10)`
tenth defect: `N₁₀ = κ₉ H³⁵`.  The defect is unsquared, so the
integral is chamber-free. -/
theorem alignedTenthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₉ : K,
      alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₉ * H ^ 35 := by
  let N : K[X] :=
    alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
      (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      H * N.derivative - (35 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      alignedTenthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC35 : Polynomial.C (35 : K) = (35 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian N (H ^ 35) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      N * (Polynomial.C (35 : K) * H ^ (35 - 1) * H.derivative) -
          N.derivative * H ^ 35 =
          H ^ 34 *
            (Polynomial.C (35 : K) * N * H.derivative -
              H * N.derivative) := by
        ring
      _ = 0 := by
        rw [hC35]
        have hfac :
            (35 : K[X]) * N * H.derivative - H * N.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 35 hH) hW

/-! ## Root decic of the factored transport and its absorption -/

/-- Evaluating a factored-transport tenth row at a root of its
co-factor: the root decic `7 g¹⁰ - 85 p₆ g⁸ + 370 p₆² g⁶ - 685 p₆³ g⁴
+ 480 p₆⁴ g² - 64 p₆⁵` vanishes there.  The decic is even in `g` with
a pure `p₆⁵` tail, so no `g`-factor splits off; it is not excluded as
an identity. -/
theorem alignedTenth_factored_rootDecic_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (1048576 : K[X]) *
        ((7 : K[X]) * g ^ 10 - (85 : K[X]) * a6 * g ^ 8 +
          (370 : K[X]) * a6 ^ 2 * g ^ 6 - (685 : K[X]) * a6 ^ 3 * g ^ 4 +
          (480 : K[X]) * a6 ^ 4 * g ^ 2 - (64 : K[X]) * a6 ^ 5) =
      W)
    {a : K} (hW : W.eval a = 0) :
    7 * (g.eval a) ^ 10 - 85 * a6.eval a * (g.eval a) ^ 8 +
      370 * (a6.eval a) ^ 2 * (g.eval a) ^ 6 -
      685 * (a6.eval a) ^ 3 * (g.eval a) ^ 4 +
      480 * (a6.eval a) ^ 4 * (g.eval a) ^ 2 -
      64 * (a6.eval a) ^ 5 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  have hs := (mul_eq_zero.mp hev).resolve_left
    (by norm_num : (1048576 : K) ≠ 0)
  linear_combination hs

/-- The root decic of the consumed degree-`7` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the tenth row adds no new root
constraint. -/
theorem alignedTenth_rootDecic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    7 * G ^ 10 - 85 * P6 * G ^ 8 + 370 * P6 ^ 2 * G ^ 6 -
      685 * P6 ^ 3 * G ^ 4 + 480 * P6 ^ 4 * G ^ 2 - 64 * P6 ^ 5 = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared tenth rows and transport co-factors -/

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the square-chamber tenth row (`H = h₀²`,
`p₇ = h₀⁴ g₁`, `h₀⁴⁰` peeled, `128 q₇ h₀²` consumed): the new `q₀`
sits at `h₀²⁶` here, i.e. at `h₀³⁰` in the cleared row. -/
def alignedTenthSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
    -(1073741824 : K[X]) * b0 * h0 ^ 26 +
    (134217728 : K[X]) * b1 * g1 * h0 ^ 22 -
    (167772160 : K[X]) * a1 * a5 * h0 ^ 20 -
    (1342177280 : K[X]) * a2 * a4 * h0 ^ 20 -
    (671088640 : K[X]) * a3 ^ 2 * h0 ^ 20 +
    (805306368 : K[X]) * a2 * b6 * h0 ^ 18 +
    (671088640 : K[X]) * a3 * b5 * h0 ^ 18 +
    (536870912 : K[X]) * a4 * b4 * h0 ^ 18 +
    (402653184 : K[X]) * a5 * b3 * h0 ^ 18 +
    (268435456 : K[X]) * b2 * a6 * h0 ^ 18 -
    (134217728 : K[X]) * b2 * g1 ^ 2 * h0 ^ 18 +
    (125829120 : K[X]) * a1 * a6 * g1 * h0 ^ 16 -
    (36700160 : K[X]) * a1 * g1 ^ 3 * h0 ^ 16 +
    (1174405120 : K[X]) * a3 * a4 * g1 * h0 ^ 16 -
    (805306368 : K[X]) * a3 * b6 * g1 * h0 ^ 14 -
    (671088640 : K[X]) * a4 * b5 * g1 * h0 ^ 14 -
    (536870912 : K[X]) * a5 * b4 * g1 * h0 ^ 14 -
    (402653184 : K[X]) * b3 * a6 * g1 * h0 ^ 14 +
    (134217728 : K[X]) * b3 * g1 ^ 3 * h0 ^ 14 -
    (125829120 : K[X]) * a2 * a6 * g1 ^ 2 * h0 ^ 12 +
    (36700160 : K[X]) * a2 * g1 ^ 4 * h0 ^ 12 +
    (167772160 : K[X]) * a3 * a5 * a6 * h0 ^ 12 +
    (671088640 : K[X]) * a4 ^ 2 * a6 * h0 ^ 12 -
    (587202560 : K[X]) * a4 ^ 2 * g1 ^ 2 * h0 ^ 12 +
    (167772160 : K[X]) * a4 * a5 ^ 2 * h0 ^ 12 -
    (805306368 : K[X]) * a4 * b6 * a6 * h0 ^ 10 +
    (805306368 : K[X]) * a4 * b6 * g1 ^ 2 * h0 ^ 10 -
    (402653184 : K[X]) * a5 ^ 2 * b6 * h0 ^ 10 -
    (671088640 : K[X]) * a5 * b5 * a6 * h0 ^ 10 +
    (671088640 : K[X]) * a5 * b5 * g1 ^ 2 * h0 ^ 10 -
    (268435456 : K[X]) * b4 * a6 ^ 2 * h0 ^ 10 +
    (536870912 : K[X]) * b4 * a6 * g1 ^ 2 * h0 ^ 10 -
    (134217728 : K[X]) * b4 * g1 ^ 4 * h0 ^ 10 -
    (125829120 : K[X]) * a3 * a6 ^ 2 * g1 * h0 ^ 8 +
    (162529280 : K[X]) * a3 * a6 * g1 ^ 3 * h0 ^ 8 -
    (36700160 : K[X]) * a3 * g1 ^ 5 * h0 ^ 8 -
    (293601280 : K[X]) * a4 * a5 * a6 * g1 * h0 ^ 8 +
    (36700160 : K[X]) * a4 * a5 * g1 ^ 3 * h0 ^ 8 +
    (335544320 : K[X]) * a5 ^ 3 * g1 * h0 ^ 8 +
    (1610612736 : K[X]) * a5 * b6 * a6 * g1 * h0 ^ 6 -
    (805306368 : K[X]) * a5 * b6 * g1 ^ 3 * h0 ^ 6 +
    (671088640 : K[X]) * b5 * a6 ^ 2 * g1 * h0 ^ 6 -
    (671088640 : K[X]) * b5 * a6 * g1 ^ 3 * h0 ^ 6 +
    (134217728 : K[X]) * b5 * g1 ^ 5 * h0 ^ 6 +
    (251658240 : K[X]) * a4 * a6 ^ 2 * g1 ^ 2 * h0 ^ 4 -
    (199229440 : K[X]) * a4 * a6 * g1 ^ 4 * h0 ^ 4 +
    (36700160 : K[X]) * a4 * g1 ^ 6 * h0 ^ 4 +
    (503316480 : K[X]) * a5 ^ 2 * a6 ^ 2 * h0 ^ 4 -
    (1551892480 : K[X]) * a5 ^ 2 * a6 * g1 ^ 2 * h0 ^ 4 +
    (550502400 : K[X]) * a5 ^ 2 * g1 ^ 4 * h0 ^ 4 +
    (268435456 : K[X]) * b6 * a6 ^ 3 * h0 ^ 2 -
    (1207959552 : K[X]) * b6 * a6 ^ 2 * g1 ^ 2 * h0 ^ 2 +
    (805306368 : K[X]) * b6 * a6 * g1 ^ 4 * h0 ^ 2 -
    (134217728 : K[X]) * b6 * g1 ^ 6 * h0 ^ 2 -
    (1048576000 : K[X]) * a5 * a6 ^ 3 * g1 +
    (1934622720 : K[X]) * a5 * a6 ^ 2 * g1 ^ 3 -
    (938475520 : K[X]) * a5 * a6 * g1 ^ 5 +
    (131072000 : K[X]) * a5 * g1 ^ 7 +
    Polynomial.C κ *
      ((33554432 : K[X]) * a0 * h0 ^ 26 -
        (4194304 : K[X]) * a1 * g1 * h0 ^ 22 -
        (33554432 : K[X]) * a2 * a6 * h0 ^ 18 +
        (4194304 : K[X]) * a2 * g1 ^ 2 * h0 ^ 18 -
        (33554432 : K[X]) * a3 * a5 * h0 ^ 18 -
        (16777216 : K[X]) * a4 ^ 2 * h0 ^ 18 +
        (37748736 : K[X]) * a3 * a6 * g1 * h0 ^ 14 -
        (4194304 : K[X]) * a3 * g1 ^ 3 * h0 ^ 14 +
        (37748736 : K[X]) * a4 * a5 * g1 * h0 ^ 14 +
        (33554432 : K[X]) * a4 * a6 ^ 2 * h0 ^ 10 -
        (41943040 : K[X]) * a4 * a6 * g1 ^ 2 * h0 ^ 10 +
        (4194304 : K[X]) * a4 * g1 ^ 4 * h0 ^ 10 +
        (33554432 : K[X]) * a5 ^ 2 * a6 * h0 ^ 10 -
        (20971520 : K[X]) * a5 ^ 2 * g1 ^ 2 * h0 ^ 10 -
        (71303168 : K[X]) * a5 * a6 ^ 2 * g1 * h0 ^ 6 +
        (46137344 : K[X]) * a5 * a6 * g1 ^ 3 * h0 ^ 6 -
        (4194304 : K[X]) * a5 * g1 ^ 5 * h0 ^ 6 -
        (8388608 : K[X]) * a6 ^ 4 * h0 ^ 2 +
        (37748736 : K[X]) * a6 ^ 3 * g1 ^ 2 * h0 ^ 2 -
        (25165824 : K[X]) * a6 ^ 2 * g1 ^ 4 * h0 ^ 2 +
        (4194304 : K[X]) * a6 * g1 ^ 6 * h0 ^ 2) -
    Polynomial.C μ *
      ((7340032 : K[X]) * a1 * h0 ^ 25 -
        (7340032 : K[X]) * a2 * g1 * h0 ^ 21 -
        (7340032 : K[X]) * a3 * a6 * h0 ^ 17 +
        (7340032 : K[X]) * a3 * g1 ^ 2 * h0 ^ 17 -
        (7340032 : K[X]) * a4 * a5 * h0 ^ 17 +
        (14680064 : K[X]) * a4 * a6 * g1 * h0 ^ 13 -
        (7340032 : K[X]) * a4 * g1 ^ 3 * h0 ^ 13 +
        (7340032 : K[X]) * a5 ^ 2 * g1 * h0 ^ 13 +
        (7340032 : K[X]) * a5 * a6 ^ 2 * h0 ^ 9 -
        (22020096 : K[X]) * a5 * a6 * g1 ^ 2 * h0 ^ 9 +
        (7340032 : K[X]) * a5 * g1 ^ 4 * h0 ^ 9 -
        (7340032 : K[X]) * a6 ^ 3 * g1 * h0 ^ 5 +
        (14680064 : K[X]) * a6 ^ 2 * g1 ^ 3 * h0 ^ 5 -
        (7340032 : K[X]) * a6 * g1 ^ 5 * h0 ^ 5 +
        (1048576 : K[X]) * g1 ^ 7 * h0 ^ 5)

/-- Cleared tenth row of the square chamber, in factored form: `h₀⁴`
times the transport co-factor plus the pure `g₁, p₆` decic block. -/
def alignedTenthSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : K[X])
    (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedTenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3
        b4 b5 b6 κ μ +
    (1048576 : K[X]) *
      ((7 : K[X]) * g1 ^ 10 - (85 : K[X]) * a6 * g1 ^ 8 +
        (370 : K[X]) * a6 ^ 2 * g1 ^ 6 - (685 : K[X]) * a6 ^ 3 * g1 ^ 4 +
        (480 : K[X]) * a6 ^ 4 * g1 ^ 2 - (64 : K[X]) * a6 ^ 5)

set_option maxHeartbeats 1600000000 in
/-- Transport co-factor of the nonsquare-chamber tenth row
(`p₇ = H² g₂`, `H²⁰` peeled, `128 q₇ H` consumed): the new `q₀` sits
at `H¹³` here, i.e. at `H¹⁵` in the cleared row. -/
def alignedTenthNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(1073741824 : K[X]) * b0 * H ^ 13 +
    (134217728 : K[X]) * b1 * g2 * H ^ 11 -
    (167772160 : K[X]) * a1 * a5 * H ^ 10 -
    (1342177280 : K[X]) * a2 * a4 * H ^ 10 -
    (671088640 : K[X]) * a3 ^ 2 * H ^ 10 +
    (805306368 : K[X]) * a2 * b6 * H ^ 9 +
    (671088640 : K[X]) * a3 * b5 * H ^ 9 +
    (536870912 : K[X]) * a4 * b4 * H ^ 9 +
    (402653184 : K[X]) * a5 * b3 * H ^ 9 +
    (268435456 : K[X]) * b2 * a6 * H ^ 9 -
    (134217728 : K[X]) * b2 * g2 ^ 2 * H ^ 9 +
    (125829120 : K[X]) * a1 * a6 * g2 * H ^ 8 -
    (36700160 : K[X]) * a1 * g2 ^ 3 * H ^ 8 +
    (1174405120 : K[X]) * a3 * a4 * g2 * H ^ 8 -
    (805306368 : K[X]) * a3 * b6 * g2 * H ^ 7 -
    (671088640 : K[X]) * a4 * b5 * g2 * H ^ 7 -
    (536870912 : K[X]) * a5 * b4 * g2 * H ^ 7 -
    (402653184 : K[X]) * b3 * a6 * g2 * H ^ 7 +
    (134217728 : K[X]) * b3 * g2 ^ 3 * H ^ 7 -
    (125829120 : K[X]) * a2 * a6 * g2 ^ 2 * H ^ 6 +
    (36700160 : K[X]) * a2 * g2 ^ 4 * H ^ 6 +
    (167772160 : K[X]) * a3 * a5 * a6 * H ^ 6 +
    (671088640 : K[X]) * a4 ^ 2 * a6 * H ^ 6 -
    (587202560 : K[X]) * a4 ^ 2 * g2 ^ 2 * H ^ 6 +
    (167772160 : K[X]) * a4 * a5 ^ 2 * H ^ 6 -
    (805306368 : K[X]) * a4 * b6 * a6 * H ^ 5 +
    (805306368 : K[X]) * a4 * b6 * g2 ^ 2 * H ^ 5 -
    (402653184 : K[X]) * a5 ^ 2 * b6 * H ^ 5 -
    (671088640 : K[X]) * a5 * b5 * a6 * H ^ 5 +
    (671088640 : K[X]) * a5 * b5 * g2 ^ 2 * H ^ 5 -
    (268435456 : K[X]) * b4 * a6 ^ 2 * H ^ 5 +
    (536870912 : K[X]) * b4 * a6 * g2 ^ 2 * H ^ 5 -
    (134217728 : K[X]) * b4 * g2 ^ 4 * H ^ 5 -
    (125829120 : K[X]) * a3 * a6 ^ 2 * g2 * H ^ 4 +
    (162529280 : K[X]) * a3 * a6 * g2 ^ 3 * H ^ 4 -
    (36700160 : K[X]) * a3 * g2 ^ 5 * H ^ 4 -
    (293601280 : K[X]) * a4 * a5 * a6 * g2 * H ^ 4 +
    (36700160 : K[X]) * a4 * a5 * g2 ^ 3 * H ^ 4 +
    (335544320 : K[X]) * a5 ^ 3 * g2 * H ^ 4 +
    (1610612736 : K[X]) * a5 * b6 * a6 * g2 * H ^ 3 -
    (805306368 : K[X]) * a5 * b6 * g2 ^ 3 * H ^ 3 +
    (671088640 : K[X]) * b5 * a6 ^ 2 * g2 * H ^ 3 -
    (671088640 : K[X]) * b5 * a6 * g2 ^ 3 * H ^ 3 +
    (134217728 : K[X]) * b5 * g2 ^ 5 * H ^ 3 +
    (251658240 : K[X]) * a4 * a6 ^ 2 * g2 ^ 2 * H ^ 2 -
    (199229440 : K[X]) * a4 * a6 * g2 ^ 4 * H ^ 2 +
    (36700160 : K[X]) * a4 * g2 ^ 6 * H ^ 2 +
    (503316480 : K[X]) * a5 ^ 2 * a6 ^ 2 * H ^ 2 -
    (1551892480 : K[X]) * a5 ^ 2 * a6 * g2 ^ 2 * H ^ 2 +
    (550502400 : K[X]) * a5 ^ 2 * g2 ^ 4 * H ^ 2 +
    (268435456 : K[X]) * b6 * a6 ^ 3 * H -
    (1207959552 : K[X]) * b6 * a6 ^ 2 * g2 ^ 2 * H +
    (805306368 : K[X]) * b6 * a6 * g2 ^ 4 * H -
    (134217728 : K[X]) * b6 * g2 ^ 6 * H -
    (1048576000 : K[X]) * a5 * a6 ^ 3 * g2 +
    (1934622720 : K[X]) * a5 * a6 ^ 2 * g2 ^ 3 -
    (938475520 : K[X]) * a5 * a6 * g2 ^ 5 +
    (131072000 : K[X]) * a5 * g2 ^ 7 +
    Polynomial.C κ *
      ((33554432 : K[X]) * a0 * H ^ 13 -
        (4194304 : K[X]) * a1 * g2 * H ^ 11 -
        (33554432 : K[X]) * a2 * a6 * H ^ 9 +
        (4194304 : K[X]) * a2 * g2 ^ 2 * H ^ 9 -
        (33554432 : K[X]) * a3 * a5 * H ^ 9 -
        (16777216 : K[X]) * a4 ^ 2 * H ^ 9 +
        (37748736 : K[X]) * a3 * a6 * g2 * H ^ 7 -
        (4194304 : K[X]) * a3 * g2 ^ 3 * H ^ 7 +
        (37748736 : K[X]) * a4 * a5 * g2 * H ^ 7 +
        (33554432 : K[X]) * a4 * a6 ^ 2 * H ^ 5 -
        (41943040 : K[X]) * a4 * a6 * g2 ^ 2 * H ^ 5 +
        (4194304 : K[X]) * a4 * g2 ^ 4 * H ^ 5 +
        (33554432 : K[X]) * a5 ^ 2 * a6 * H ^ 5 -
        (20971520 : K[X]) * a5 ^ 2 * g2 ^ 2 * H ^ 5 -
        (71303168 : K[X]) * a5 * a6 ^ 2 * g2 * H ^ 3 +
        (46137344 : K[X]) * a5 * a6 * g2 ^ 3 * H ^ 3 -
        (4194304 : K[X]) * a5 * g2 ^ 5 * H ^ 3 -
        (8388608 : K[X]) * a6 ^ 4 * H +
        (37748736 : K[X]) * a6 ^ 3 * g2 ^ 2 * H -
        (25165824 : K[X]) * a6 ^ 2 * g2 ^ 4 * H +
        (4194304 : K[X]) * a6 * g2 ^ 6 * H)

/-- Cleared tenth row of the nonsquare chamber, in factored form: `H²`
times the transport co-factor plus the pure `g₂, p₆` decic block. -/
def alignedTenthNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedTenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3
        b4 b5 b6 κ +
    (1048576 : K[X]) *
      ((7 : K[X]) * g2 ^ 10 - (85 : K[X]) * a6 * g2 ^ 8 +
        (370 : K[X]) * a6 ^ 2 * g2 ^ 6 - (685 : K[X]) * a6 ^ 3 * g2 ^ 4 +
        (480 : K[X]) * a6 ^ 4 * g2 ^ 2 - (64 : K[X]) * a6 ^ 5)

/-! ## Square chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀⁴⁰` from `N₁₀ = κ₉ H³⁵` on `H = h₀²`, `p₇ = h₀⁴ g₁` and
consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `7340032 p₁ h₀²⁰ - 7340032 p₂ g₁ h₀¹⁶
- 7340032 p₃ p₆ h₀¹² + 7340032 p₃ g₁² h₀¹² - 7340032 p₄ p₅ h₀¹²
+ 14680064 p₄ p₆ g₁ h₀⁸ - 7340032 p₄ g₁³ h₀⁸ + 7340032 p₅² g₁ h₀⁸
+ 7340032 p₅ p₆² h₀⁴ - 22020096 p₅ p₆ g₁² h₀⁴ + 7340032 p₅ g₁⁴ h₀⁴
- 7340032 p₆³ g₁ + 14680064 p₆² g₁³ - 7340032 p₆ g₁⁵ + 1048576 g₁⁷`,
leaves the cleared tenth row of the square chamber together with its
factored transport form.  Nothing is forced: `κ₉` is preserved, not
cleared. -/
theorem alignedSquareTenth_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₉ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hN : alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₉ * H ^ 35)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedTenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4
        b5 b6 κ μ =
      Polynomial.C κ₉ * h0 ^ 30 ∧
    (1048576 : K[X]) *
        ((7 : K[X]) * g1 ^ 10 - (85 : K[X]) * a6 * g1 ^ 8 +
          (370 : K[X]) * a6 ^ 2 * g1 ^ 6 - (685 : K[X]) * a6 ^ 3 * g1 ^ 4 +
          (480 : K[X]) * a6 ^ 4 * g1 ^ 2 - (64 : K[X]) * a6 ^ 5) =
      h0 ^ 4 *
        (Polynomial.C κ₉ * h0 ^ 26 -
          alignedTenthSquareCof810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2
            b3 b4 b5 b6 κ μ) := by
  have hN' := hN
  simp only [alignedTenthDefect810, hHsq, hg] at hN'
  have hclear :
      alignedTenthSquareRow810 h0 g1 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3
          b4 b5 b6 κ μ =
        Polynomial.C κ₉ * h0 ^ 30 := by
    simp only [alignedTenthSquareRow810, alignedTenthSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 40 hh0)
    linear_combination hN' -
      h0 ^ 40 *
        ((7340032 : K[X]) * a1 * h0 ^ 20 -
        (7340032 : K[X]) * a2 * g1 * h0 ^ 16 -
        (7340032 : K[X]) * a3 * a6 * h0 ^ 12 +
        (7340032 : K[X]) * a3 * g1 ^ 2 * h0 ^ 12 -
        (7340032 : K[X]) * a4 * a5 * h0 ^ 12 +
        (14680064 : K[X]) * a4 * a6 * g1 * h0 ^ 8 -
        (7340032 : K[X]) * a4 * g1 ^ 3 * h0 ^ 8 +
        (7340032 : K[X]) * a5 ^ 2 * g1 * h0 ^ 8 +
        (7340032 : K[X]) * a5 * a6 ^ 2 * h0 ^ 4 -
        (22020096 : K[X]) * a5 * a6 * g1 ^ 2 * h0 ^ 4 +
        (7340032 : K[X]) * a5 * g1 ^ 4 * h0 ^ 4 -
        (7340032 : K[X]) * a6 ^ 3 * g1 +
        (14680064 : K[X]) * a6 ^ 2 * g1 ^ 3 -
        (7340032 : K[X]) * a6 * g1 ^ 5 +
        (1048576 : K[X]) * g1 ^ 7) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedTenthSquareRow810] at hclear
  linear_combination hclear

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `H²⁰` from `N₁₀ = κ₉ H³⁵` on `p₇ = H² g₂` and consuming
the previous factored quotient (`128 q₇ H` solved) with the mate
`7340032 p₁ H¹⁰ - 7340032 p₂ g₂ H⁸ - 7340032 p₃ p₆ H⁶ + 7340032 p₃ g₂² H⁶
- 7340032 p₄ p₅ H⁶ + 14680064 p₄ p₆ g₂ H⁴ - 7340032 p₄ g₂³ H⁴
+ 7340032 p₅² g₂ H⁴ + 7340032 p₅ p₆² H² - 22020096 p₅ p₆ g₂² H²
+ 7340032 p₅ g₂⁴ H² - 7340032 p₆³ g₂ + 14680064 p₆² g₂³ - 7340032 p₆ g₂⁵
+ 1048576 g₂⁷`, leaves the cleared tenth row of the nonsquare chamber
together with its factored transport form.  The unsquared integral
forces nothing: `κ₉` is preserved, not cleared. -/
theorem alignedNonsquareTenth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₉ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hN : alignedTenthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3
        b4 b5 b6 b7 κ =
      Polynomial.C κ₉ * H ^ 35)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedTenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3
        b4 b5 b6 κ =
      Polynomial.C κ₉ * H ^ 15 ∧
    (1048576 : K[X]) *
        ((7 : K[X]) * g2 ^ 10 - (85 : K[X]) * a6 * g2 ^ 8 +
          (370 : K[X]) * a6 ^ 2 * g2 ^ 6 - (685 : K[X]) * a6 ^ 3 * g2 ^ 4 +
          (480 : K[X]) * a6 ^ 4 * g2 ^ 2 - (64 : K[X]) * a6 ^ 5) =
      H ^ 2 *
        (Polynomial.C κ₉ * H ^ 13 -
          alignedTenthNonsquareCof810 H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1
            b2 b3 b4 b5 b6 κ) := by
  have hN' := hN
  simp only [alignedTenthDefect810, hg2] at hN'
  have hclear :
      alignedTenthNonsquareRow810 H g2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3
          b4 b5 b6 κ =
        Polynomial.C κ₉ * H ^ 15 := by
    simp only [alignedTenthNonsquareRow810, alignedTenthNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 20 hH)
    linear_combination hN' -
      H ^ 20 *
        ((7340032 : K[X]) * a1 * H ^ 10 -
        (7340032 : K[X]) * a2 * g2 * H ^ 8 -
        (7340032 : K[X]) * a3 * a6 * H ^ 6 +
        (7340032 : K[X]) * a3 * g2 ^ 2 * H ^ 6 -
        (7340032 : K[X]) * a4 * a5 * H ^ 6 +
        (14680064 : K[X]) * a4 * a6 * g2 * H ^ 4 -
        (7340032 : K[X]) * a4 * g2 ^ 3 * H ^ 4 +
        (7340032 : K[X]) * a5 ^ 2 * g2 * H ^ 4 +
        (7340032 : K[X]) * a5 * a6 ^ 2 * H ^ 2 -
        (22020096 : K[X]) * a5 * a6 * g2 ^ 2 * H ^ 2 +
        (7340032 : K[X]) * a5 * g2 ^ 4 * H ^ 2 -
        (7340032 : K[X]) * a6 ^ 3 * g2 +
        (14680064 : K[X]) * a6 ^ 2 * g2 ^ 3 -
        (7340032 : K[X]) * a6 * g2 ^ 5 +
        (1048576 : K[X]) * g2 ^ 7) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedTenthNonsquareRow810] at hclear
  linear_combination hclear

/-! ## Source-facing tenth-row packets -/

/-- Source-facing weight-seventy integral of a normalized aligned
scale-two `(8,10)` source: the degree-`7` row is consumed into
`N₁₀ = κ₉ H³⁵` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedTenthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ : K),
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
          Polynomial.C κ₉ * H ^ 35 := by
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
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, aligned_q9_solved_810 haligned,
    hM, hE4, hF2, hG, hI2, hJ, hL2, hN10⟩

/-- Exact square-chamber tenth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`7`
row gives the cleared tenth row (with the new `q₀` at `h₀³⁰`) against
the preserved `κ₉`, the carried root collapse `g₁ = p₆ = 0`, and the
carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedTenthFace_squareChamber_packet
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
    ∃ (κ μ κ₉ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        alignedTenthSquareRow810 h0 g1 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) κ μ =
          Polynomial.C κ₉ * h0 ^ 30 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 35 := by
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
  obtain ⟨κ₉, hNrel⟩ :=
    alignedTenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hsolved10, _hfact10⟩ :=
    alignedSquareTenth_solved_810 hh0 hHsq hp7 hNrel hcore
  exact ⟨κ, μ, κ₉, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hsolved10,
    hcollapse, hdvdg1, hdvdp6, hNrel⟩

/-- Exact nonsquare-chamber tenth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂` and the previous
packet, the consumed degree-`7` row gives the cleared tenth row (with
the new `q₀` at `H¹⁵`) against the preserved `κ₉`, the carried root
collapse `g₂ = p₆ = 0` at every (simple) root of the core, and the
carried descents `H ∣ g₂`, `H ∣ p₆`.  The unsquared integral forces
nothing: `κ₉` is not cleared. -/
theorem normalized810ScaleTwo_alignedTenthFace_nonsquareChamber_packet
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
    ∃ (κ κ₉ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        alignedTenthNonsquareRow810 H g2 (p.coeff 0) (p.coeff 1)
            (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) κ =
          Polynomial.C κ₉ * H ^ 15 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedTenthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₉ * H ^ 35 := by
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
  obtain ⟨κ₉, hNrel⟩ :=
    alignedTenthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨hclear10, _hfact10⟩ :=
    alignedNonsquareTenth_solved_810 hH hg2 hNrel hfac
  exact ⟨κ, κ₉, g2, hg2, by rw [hq9, hg2]; ring, hclear10,
    hcollapse, hdvdg2, hdvdp6, hNrel⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`7`
aligned row, carrying the factored transport of the decic block.
Neither chamber is excluded, the constants `κ`, `μ`, `κ₉` are
preserved (nothing is forced by the unsquared integral), and no
closure is claimed. -/
theorem normalized810ScaleTwo_alignedTenthFace_chamberDichotomy
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
      ∃ (κ μ κ₉ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (1048576 : K[X]) *
              ((7 : K[X]) * g1 ^ 10 -
                (85 : K[X]) * p.coeff 6 * g1 ^ 8 +
                (370 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 6 -
                (685 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 4 +
                (480 : K[X]) * p.coeff 6 ^ 4 * g1 ^ 2 -
                (64 : K[X]) * p.coeff 6 ^ 5) =
            h0 ^ 4 *
              (Polynomial.C κ₉ * h0 ^ 26 -
                alignedTenthSquareCof810 h0 g1 (p.coeff 0) (p.coeff 1)
                  (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
                  (p.coeff 6) (q.coeff 0) (q.coeff 1) (q.coeff 2)
                  (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
                  κ μ) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₉ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (1048576 : K[X]) *
              ((7 : K[X]) * g2 ^ 10 -
                (85 : K[X]) * p.coeff 6 * g2 ^ 8 +
                (370 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 6 -
                (685 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 4 +
                (480 : K[X]) * p.coeff 6 ^ 4 * g2 ^ 2 -
                (64 : K[X]) * p.coeff 6 ^ 5) =
            H ^ 2 *
              (Polynomial.C κ₉ * H ^ 13 -
                alignedTenthNonsquareCof810 H g2 (p.coeff 0) (p.coeff 1)
                  (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
                  (p.coeff 6) (q.coeff 0) (q.coeff 1) (q.coeff 2)
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
      normalized810ScaleTwo_alignedTenthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₉, g1, hp7, hq9, hsolved10,
      hcollapse, hdvdg1, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₉, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedTenthSquareRow810] at hsolved10
    linear_combination hsolved10
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedTenthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₉, g2, hp7, hq9, hclear10, hcollapse,
      hdvdg2, hdvdp6, _hNrel⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, κ₉, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedTenthNonsquareRow810] at hclear10
    linear_combination hclear10

/-- Chamber-independent root jet after the consumed degree-`7` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its decic content is absorbed by the
degree-`13` collapse (`alignedTenth_rootDecic_absorbed_810`) — and the
new coefficient `q₀` is tied into the cleared tenth row instead of
being killed. -/
theorem normalized810ScaleTwo_alignedTenthFace_rootJet
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
  normalized810ScaleTwo_alignedNinthFace_rootJet hsource haligned

#print axioms alignedTenthCoefficientJacobianRow_810
#print axioms alignedTenthDefect_weightedDerivative_identity_810
#print axioms alignedTenthDefectRow_eq_zero_810
#print axioms alignedTenthDefectPowerRelation_810
#print axioms alignedTenth_factored_rootDecic_810
#print axioms alignedTenth_rootDecic_absorbed_810
#print axioms alignedSquareTenth_solved_810
#print axioms alignedNonsquareTenth_solved_810
#print axioms normalized810ScaleTwo_alignedTenthFace_packet
#print axioms normalized810ScaleTwo_alignedTenthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedTenthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedTenthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedTenthFace_rootJet

end Max11DegreeRoutes
