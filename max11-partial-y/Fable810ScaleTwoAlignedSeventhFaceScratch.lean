import Fable810ScaleTwoAlignedSixthFaceScratch

/-! # Seventh aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedSixthFaceScratch` consumed the degree-`10`
aligned Keller row (the chambered `I² = κ₆ H⁴⁹`).  This file consumes
the next unused aligned row, the degree-`9` Jacobian coefficient — the
first row that sees `p₀` and `q₂` (internal names `alignedEighth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, `H G' - 21 G H' = 0`,
`2 H I' - 49 I H' = 0`, the degree-`9` row is the weighted derivative
of the weight-fifty-six defect

`J = 41943040 p₀ H²⁸ - 33554432 q₂ H²⁷ - 5242880 p₁ p₇ H²⁴
  - 10485760 p₂ p₆ H²⁴ - 52428800 p₃ p₅ H²⁴ - 26214400 p₄² H²⁴
  + 29360128 p₃ q₇ H²³ + 25165824 p₄ q₆ H²³ + 20971520 p₅ q₅ H²³
  + 12582912 q₃ p₇ H²³ + 16777216 q₄ p₆ H²³ + 5242880 p₂ p₇² H²⁰
  + 6553600 p₃ p₆ p₇ H²⁰ + 58982400 p₄ p₅ p₇ H²⁰ + 6553600 p₄ p₆² H²⁰
  + 32768000 p₅² p₆ H²⁰ - 36700160 p₄ q₇ p₇ H¹⁹ - 31457280 p₅ q₆ p₇ H¹⁹
  - 36700160 p₅ q₇ p₆ H¹⁹ - 10485760 q₄ p₇² H¹⁹ - 26214400 q₅ p₆ p₇ H¹⁹
  - 15728640 q₆ p₆² H¹⁹ - 4096000 p₃ p₇³ H¹⁶ - 6553600 p₄ p₆ p₇² H¹⁶
  - 32768000 p₅² p₇² H¹⁶ - 7372800 p₅ p₆² p₇ H¹⁶ + 3686400 p₆⁴ H¹⁶
  + 41287680 p₅ q₇ p₇² H¹⁵ + 9830400 q₅ p₇³ H¹⁵ + 35389440 q₆ p₆ p₇² H¹⁵
  + 41287680 q₇ p₆² p₇ H¹⁵ + 3379200 p₄ p₇⁴ H¹² + 6758400 p₅ p₆ p₇³ H¹²
  - 29491200 p₆³ p₇² H¹² - 9584640 q₆ p₇⁴ H¹¹ - 44728320 q₇ p₆ p₇³ H¹¹
  - 2895360 p₅ p₇⁵ H⁸ + 30451200 p₆² p₇⁴ H⁸ + 9504768 q₇ p₇⁵ H⁷
  - 9335040 p₆ p₇⁶ H⁴ + 835380 p₇⁸
  + κ (1048576 p₂ H²⁷ - 1310720 p₃ p₇ H²³ - 1310720 p₄ p₆ H²³
       - 655360 p₅² H²³ + 1474560 p₄ p₇² H¹⁹ + 2949120 p₅ p₆ p₇ H¹⁹
       + 491520 p₆³ H¹⁹ - 1597440 p₅ p₇³ H¹⁵ - 2396160 p₆² p₇² H¹⁵
       + 1697280 p₆ p₇⁴ H¹¹ - 297024 p₇⁶ H⁷)`,

via the exact multiplier identity

`4194304 H²⁴ H⁴ · row₉[p₈ = H⁴, q₁₀ = H⁵] = (H J' - 28 J H')
  - 9437184 H²⁴ p₁' N + 1048576 H²⁴ p₁ N'
  + (1048576 H²¹ p₂' + 786432 p₂ H²⁰ H') C - 262144 H²¹ p₂ C'
  + (163840 p₃ H¹⁶ + 143360 p₄ p₇ H¹² + 143360 p₅ p₆ H¹²
     - 8960 p₅ p₇² H⁸ - 8960 p₆² p₇ H⁸ + 3360 p₆ p₇³ H⁴ - 357 p₇⁵)
    (2 H D' - 21 D H')
  + (20480 p₄ H¹² + 15360 p₅ p₇ H⁸ + 7680 p₆² H⁸ - 1920 p₆ p₇² H⁴
     + 200 p₇⁴) (H E' - 14 E H')
  + (1280 p₅ H⁸ + 800 p₆ p₇ H⁴ - 50 p₇³) (2 H F' - 35 F H')
  + (640 p₆ H⁴ + 160 p₇²) (H G' - 21 G H')
  + 5 p₇ (2 H I' - 49 I H')`.

On the aligned face every right-hand correction vanishes, so
`H J' = 28 J H'` and the weight-fifty-six first integral

`J = κ₇ H²⁸`

holds for a preserved constant `κ₇`.  The exponent is even, so — exactly
as for the degree-`13` and degree-`11` rows — the integral is
**chamber-free**: neither chamber forces anything, and `κ₇` is
preserved in both.

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: peeling `h₀³²` and consuming
  the previous factored quotient (`128 q₇ h₀²` solved, transported by
  the mate `229376 p₃ h₀¹² - 286720 p₄ g₁ h₀⁸ - 286720 p₅ p₆ h₀⁴
  + 322560 p₅ g₁² h₀⁴ + 322560 p₆² g₁ - 349440 p₆ g₁³ + 74256 g₁⁵`)
  leaves the cleared eighth row with `p₀` at `h₀²⁴` and `q₂` at `h₀²²`
  against `κ₇ h₀²⁴`, and the factored transport
  `300 (1547 g₁⁸ - 15392 p₆ g₁⁶ + 49536 p₆² g₁⁴ - 55296 p₆³ g₁²
   + 12288 p₆⁴) = h₀⁴ · (κ₇ h₀²⁰ - co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): with
  `p₇ = H² g₂`, peeling `H¹⁶` and consuming the previous factored
  quotient (same mate) leaves the cleared eighth row (with `p₀` at
  `H¹²` and `q₂` at `H¹¹`) against `κ₇ H¹²` and the transport
  `300 (1547 g₂⁸ - 15392 p₆ g₂⁶ + 49536 p₆² g₂⁴ - 55296 p₆³ g₂²
   + 12288 p₆⁴) = H² · (κ₇ H¹⁰ - co-factor)`.

At a root of the transport co-factor the honest root branch is the
root octic `1547 g⁸ - 15392 p₆ g⁶ + 49536 p₆² g⁴ - 55296 p₆³ g²
+ 12288 p₆⁴ = 0` — no `g`-factor splits off, since the block is even
in `g`.  Like the quartic, quintic, sextic, and septic of the previous
rows it adds *no new* root information: the consumed degree-`13` row
already collapsed `g(a) = 0 ∧ p₆(a) = 0` at every core root, and that
collapse absorbs the octic identically
(`alignedEighth_rootOctic_absorbed_810`).  The chamber-independent root
jet therefore stays `p₇, q₉, q₈, p₆` — the row ties the new
coefficients `p₀, q₂` into the cleared eighth row (at `h₀²⁴`/`h₀²²`,
resp. `H¹²`/`H¹¹`) instead of killing anything new at the root.

No closure is claimed.  Both chambers remain open, the constants `κ`,
`μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆`, and the new `κ₇` are preserved and not
cleared, the zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`,
`κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`, `κ₇ = 0`) are not excluded as
polynomial identities, the deepened quotients `g₁/h₀`, `p₆/h₀`,
`g₂/H`, `p₆/H` from the degree-`13` face are still not re-cleared
through the tower here, the root octic is recorded but not excluded as
an identity, and no individual vanishing of `p₀`, `p₁`, `p₂`, `p₃`,
`p₄`, `p₅`, `q₂`, `q₃`, `q₄`, `q₅`, `q₆`, `q₇` is claimed.  The next
unused Keller row on the aligned face is the degree-`8` Jacobian
coefficient, the first row that sees `q₁` (weight-sixty-three defect,
odd exponent, hence chambered).  No total-degree or twice-prime
theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`9` Keller coefficient on the aligned face -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`9` Jacobian coefficient, the first
aligned row that sees `p₀` and `q₂`. -/
theorem alignedEighthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 7).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 6).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 2).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 3).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 8).derivative +
        p.coeff 1 * (q.coeff 9).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 9) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (9 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 9 :
      Finset (ℕ × ℕ)) =
      ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3),
        (7, 2), (8, 1), (9, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10]
  linear_combination hcoeff

/-! ## Aligned eighth defect -/

/-- Weight-fifty-six defect of the degree-`9` aligned `(8,10)` row.
On the aligned face it is a polynomial first integral of even weight
fifty-six, hence chamber-free. -/
def alignedEighthDefect810 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  (41943040 : K[X]) * a0 * H ^ 28 -
    (33554432 : K[X]) * b2 * H ^ 27 -
    (5242880 : K[X]) * a1 * a7 * H ^ 24 -
    (10485760 : K[X]) * a2 * a6 * H ^ 24 -
    (52428800 : K[X]) * a3 * a5 * H ^ 24 -
    (26214400 : K[X]) * a4 ^ 2 * H ^ 24 +
    (29360128 : K[X]) * a3 * b7 * H ^ 23 +
    (25165824 : K[X]) * a4 * b6 * H ^ 23 +
    (20971520 : K[X]) * a5 * b5 * H ^ 23 +
    (12582912 : K[X]) * b3 * a7 * H ^ 23 +
    (16777216 : K[X]) * b4 * a6 * H ^ 23 +
    (5242880 : K[X]) * a2 * a7 ^ 2 * H ^ 20 +
    (6553600 : K[X]) * a3 * a6 * a7 * H ^ 20 +
    (58982400 : K[X]) * a4 * a5 * a7 * H ^ 20 +
    (6553600 : K[X]) * a4 * a6 ^ 2 * H ^ 20 +
    (32768000 : K[X]) * a5 ^ 2 * a6 * H ^ 20 -
    (36700160 : K[X]) * a4 * b7 * a7 * H ^ 19 -
    (31457280 : K[X]) * a5 * b6 * a7 * H ^ 19 -
    (36700160 : K[X]) * a5 * b7 * a6 * H ^ 19 -
    (10485760 : K[X]) * b4 * a7 ^ 2 * H ^ 19 -
    (26214400 : K[X]) * b5 * a6 * a7 * H ^ 19 -
    (15728640 : K[X]) * b6 * a6 ^ 2 * H ^ 19 -
    (4096000 : K[X]) * a3 * a7 ^ 3 * H ^ 16 -
    (6553600 : K[X]) * a4 * a6 * a7 ^ 2 * H ^ 16 -
    (32768000 : K[X]) * a5 ^ 2 * a7 ^ 2 * H ^ 16 -
    (7372800 : K[X]) * a5 * a6 ^ 2 * a7 * H ^ 16 +
    (3686400 : K[X]) * a6 ^ 4 * H ^ 16 +
    (41287680 : K[X]) * a5 * b7 * a7 ^ 2 * H ^ 15 +
    (9830400 : K[X]) * b5 * a7 ^ 3 * H ^ 15 +
    (35389440 : K[X]) * b6 * a6 * a7 ^ 2 * H ^ 15 +
    (41287680 : K[X]) * b7 * a6 ^ 2 * a7 * H ^ 15 +
    (3379200 : K[X]) * a4 * a7 ^ 4 * H ^ 12 +
    (6758400 : K[X]) * a5 * a6 * a7 ^ 3 * H ^ 12 -
    (29491200 : K[X]) * a6 ^ 3 * a7 ^ 2 * H ^ 12 -
    (9584640 : K[X]) * b6 * a7 ^ 4 * H ^ 11 -
    (44728320 : K[X]) * b7 * a6 * a7 ^ 3 * H ^ 11 -
    (2895360 : K[X]) * a5 * a7 ^ 5 * H ^ 8 +
    (30451200 : K[X]) * a6 ^ 2 * a7 ^ 4 * H ^ 8 +
    (9504768 : K[X]) * b7 * a7 ^ 5 * H ^ 7 -
    (9335040 : K[X]) * a6 * a7 ^ 6 * H ^ 4 +
    (835380 : K[X]) * a7 ^ 8 +
      Polynomial.C κ *
        ((1048576 : K[X]) * a2 * H ^ 27 -
          (1310720 : K[X]) * a3 * a7 * H ^ 23 -
          (1310720 : K[X]) * a4 * a6 * H ^ 23 -
          (655360 : K[X]) * a5 ^ 2 * H ^ 23 +
          (1474560 : K[X]) * a4 * a7 ^ 2 * H ^ 19 +
          (2949120 : K[X]) * a5 * a6 * a7 * H ^ 19 +
          (491520 : K[X]) * a6 ^ 3 * H ^ 19 -
          (1597440 : K[X]) * a5 * a7 ^ 3 * H ^ 15 -
          (2396160 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 15 +
          (1697280 : K[X]) * a6 * a7 ^ 4 * H ^ 11 -
          (297024 : K[X]) * a7 ^ 6 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`9` Jacobian expression with the
weighted derivative of `J`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, degree-`12`, degree-`11`, and degree-`10`
rows. -/
theorem alignedEighthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (4194304 : K[X]) * H ^ 24 *
        ((H ^ 4).derivative * (b2 * (2 : K[X])) +
          a7.derivative * (b3 * (3 : K[X])) +
          a6.derivative * (b4 * (4 : K[X])) +
          a5.derivative * (b5 * (5 : K[X])) +
          a4.derivative * (b6 * (6 : K[X])) +
          a3.derivative * (b7 * (7 : K[X])) +
          a2.derivative * (b8 * (8 : K[X])) +
          a1.derivative * (b9 * (9 : K[X])) +
          a0.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b2.derivative +
          (a7 * (7 : K[X])) * b3.derivative +
          (a6 * (6 : K[X])) * b4.derivative +
          (a5 * (5 : K[X])) * b5.derivative +
          (a4 * (4 : K[X])) * b6.derivative +
          (a3 * (3 : K[X])) * b7.derivative +
          (a2 * (2 : K[X])) * b8.derivative +
          a1 * b9.derivative)) =
      (H *
          (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5
            b6 b7 κ).derivative -
        (28 : K[X]) *
          alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5
            b6 b7 κ * H.derivative) -
        (9437184 : K[X]) * H ^ 24 * a1.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (1048576 : K[X]) * H ^ 24 * a1 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((1048576 : K[X]) * H ^ 21 * a2.derivative +
            (786432 : K[X]) * a2 * H ^ 20 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (262144 : K[X]) * H ^ 21 * a2 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((163840 : K[X]) * a3 * H ^ 16 +
            (143360 : K[X]) * a4 * a7 * H ^ 12 +
            (143360 : K[X]) * a5 * a6 * H ^ 12 -
            (8960 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (8960 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (3360 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (357 : K[X]) * a7 ^ 5) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((20480 : K[X]) * a4 * H ^ 12 +
            (15360 : K[X]) * a5 * a7 * H ^ 8 +
            (7680 : K[X]) * a6 ^ 2 * H ^ 8 -
            (1920 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (200 : K[X]) * a7 ^ 4) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((1280 : K[X]) * a5 * H ^ 8 + (800 : K[X]) * a6 * a7 * H ^ 4 -
            (50 : K[X]) * a7 ^ 3) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((640 : K[X]) * a6 * H ^ 4 + (160 : K[X]) * a7 ^ 2) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        (5 : K[X]) * a7 *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) := by
  simp only [alignedEighthDefect810, alignedSeventhDefect810,
    alignedSixthDefect810, alignedFifthDefect810, alignedFourthDefect810,
    alignedThirdDefect810,
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

/-- On the aligned face, with the consumed degree-`15` through
degree-`10` rows, the degree-`9` row is the weighted derivative
`H J' - 28 J H' = 0`. -/
theorem alignedEighthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H *
        (alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ).derivative -
      (28 : K[X]) *
        alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEighthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10] at hrow
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
  have hid := alignedEighthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) (q.coeff 8)
    (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD, hrowE, hrowF, hrowG, hrowI] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-fifty-six polynomial first integral of the aligned `(8,10)`
eighth defect: `J = κ₇ H²⁸`.  The exponent is even, so the integral is
chamber-free. -/
theorem alignedEighthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₇ : K,
      alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ =
        Polynomial.C κ₇ * H ^ 28 := by
  let J : K[X] :=
    alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) κ
  have hrow :
      H * J.derivative - (28 : K[X]) * J * H.derivative = 0 := by
    simpa only [J] using
      alignedEighthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC28 : Polynomial.C (28 : K) = (28 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian J (H ^ 28) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      J * (Polynomial.C (28 : K) * H ^ (28 - 1) * H.derivative) -
          J.derivative * H ^ 28 =
          H ^ 27 *
            (Polynomial.C (28 : K) * J * H.derivative -
              H * J.derivative) := by
        ring
      _ = 0 := by
        rw [hC28]
        have hfac :
            (28 : K[X]) * J * H.derivative - H * J.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 28 hH) hW

/-! ## Root octic of the factored transport and its absorption -/

/-- Evaluating a factored-transport eighth row at a root of its
co-factor: the root octic `1547 g⁸ - 15392 p₆ g⁶ + 49536 p₆² g⁴
- 55296 p₆³ g² + 12288 p₆⁴` vanishes there.  The octic is even in `g`,
so no `g`-factor splits off; it is not excluded as an identity. -/
theorem alignedEighth_factored_rootOctic_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (300 : K[X]) *
        ((1547 : K[X]) * g ^ 8 - (15392 : K[X]) * a6 * g ^ 6 +
          (49536 : K[X]) * a6 ^ 2 * g ^ 4 -
          (55296 : K[X]) * a6 ^ 3 * g ^ 2 + (12288 : K[X]) * a6 ^ 4) =
      W)
    {a : K} (hW : W.eval a = 0) :
    1547 * (g.eval a) ^ 8 - 15392 * a6.eval a * (g.eval a) ^ 6 +
      49536 * (a6.eval a) ^ 2 * (g.eval a) ^ 4 -
      55296 * (a6.eval a) ^ 3 * (g.eval a) ^ 2 +
      12288 * (a6.eval a) ^ 4 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  have hs := (mul_eq_zero.mp hev).resolve_left
    (by norm_num : (300 : K) ≠ 0)
  linear_combination hs

/-- The root octic of the consumed degree-`9` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the eighth row adds no new root
constraint. -/
theorem alignedEighth_rootOctic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    1547 * G ^ 8 - 15392 * P6 * G ^ 6 + 49536 * P6 ^ 2 * G ^ 4 -
      55296 * P6 ^ 3 * G ^ 2 + 12288 * P6 ^ 4 = 0 := by
  rw [hG, hP6]
  ring

/-! ## Square chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀³²` from `J = κ₇ H²⁸` on `H = h₀²`, `p₇ = h₀⁴ g₁` and
consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `229376 p₃ h₀¹² - 286720 p₄ g₁ h₀⁸
- 286720 p₅ p₆ h₀⁴ + 322560 p₅ g₁² h₀⁴ + 322560 p₆² g₁
- 349440 p₆ g₁³ + 74256 g₁⁵`, leaves the cleared eighth row of the
square chamber (the factored transport form is an exact rearrangement,
carried by the chamber dichotomy).  The even exponent forces nothing:
`κ₇` is preserved, not cleared. -/
theorem alignedSquareEighth_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ κ₇ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hJ : alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5
        b6 b7 κ =
      Polynomial.C κ₇ * H ^ 28)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    ((41943040 : K[X]) * a0 * h0 ^ 24 -
        (33554432 : K[X]) * b2 * h0 ^ 22 -
        (5242880 : K[X]) * a1 * g1 * h0 ^ 20 +
        (12582912 : K[X]) * b3 * g1 * h0 ^ 18 -
        (10485760 : K[X]) * a2 * a6 * h0 ^ 16 +
        (5242880 : K[X]) * a2 * g1 ^ 2 * h0 ^ 16 -
        (15728640 : K[X]) * a3 * a5 * h0 ^ 16 -
        (26214400 : K[X]) * a4 ^ 2 * h0 ^ 16 +
        (25165824 : K[X]) * a4 * b6 * h0 ^ 14 +
        (20971520 : K[X]) * a5 * b5 * h0 ^ 14 +
        (16777216 : K[X]) * b4 * a6 * h0 ^ 14 -
        (10485760 : K[X]) * b4 * g1 ^ 2 * h0 ^ 14 +
        (15728640 : K[X]) * a3 * a6 * g1 * h0 ^ 12 -
        (5242880 : K[X]) * a3 * g1 ^ 3 * h0 ^ 12 +
        (13107200 : K[X]) * a4 * a5 * g1 * h0 ^ 12 -
        (31457280 : K[X]) * a5 * b6 * g1 * h0 ^ 10 -
        (26214400 : K[X]) * b5 * a6 * g1 * h0 ^ 10 +
        (9830400 : K[X]) * b5 * g1 ^ 3 * h0 ^ 10 +
        (6553600 : K[X]) * a4 * a6 ^ 2 * h0 ^ 8 -
        (18022400 : K[X]) * a4 * a6 * g1 ^ 2 * h0 ^ 8 +
        (4812800 : K[X]) * a4 * g1 ^ 4 * h0 ^ 8 -
        (13107200 : K[X]) * a5 ^ 2 * a6 * h0 ^ 8 +
        (18841600 : K[X]) * a5 ^ 2 * g1 ^ 2 * h0 ^ 8 -
        (15728640 : K[X]) * b6 * a6 ^ 2 * h0 ^ 6 +
        (35389440 : K[X]) * b6 * a6 * g1 ^ 2 * h0 ^ 6 -
        (9584640 : K[X]) * b6 * g1 ^ 4 * h0 ^ 6 +
        (32768000 : K[X]) * a5 * a6 ^ 2 * g1 * h0 ^ 4 -
        (34816000 : K[X]) * a5 * a6 * g1 ^ 3 * h0 ^ 4 +
        (7372800 : K[X]) * a5 * g1 ^ 5 * h0 ^ 4 +
        (3686400 : K[X]) * a6 ^ 4 -
        (16588800 : K[X]) * a6 ^ 3 * g1 ^ 2 +
        (14860800 : K[X]) * a6 ^ 2 * g1 ^ 4 -
        (4617600 : K[X]) * a6 * g1 ^ 6 +
        (464100 : K[X]) * g1 ^ 8 +
          Polynomial.C κ *
            ((1048576 : K[X]) * a2 * h0 ^ 22 -
              (393216 : K[X]) * a3 * g1 * h0 ^ 18 -
              (1310720 : K[X]) * a4 * a6 * h0 ^ 14 +
              (327680 : K[X]) * a4 * g1 ^ 2 * h0 ^ 14 -
              (655360 : K[X]) * a5 ^ 2 * h0 ^ 14 +
              (1802240 : K[X]) * a5 * a6 * g1 * h0 ^ 10 -
              (307200 : K[X]) * a5 * g1 ^ 3 * h0 ^ 10 +
              (491520 : K[X]) * a6 ^ 3 * h0 ^ 6 -
              (1105920 : K[X]) * a6 ^ 2 * g1 ^ 2 * h0 ^ 6 +
              (299520 : K[X]) * a6 * g1 ^ 4 * h0 ^ 6) -
          Polynomial.C μ *
            ((229376 : K[X]) * a3 * h0 ^ 21 -
              (286720 : K[X]) * a4 * g1 * h0 ^ 17 -
              (286720 : K[X]) * a5 * a6 * h0 ^ 13 +
              (322560 : K[X]) * a5 * g1 ^ 2 * h0 ^ 13 +
              (322560 : K[X]) * a6 ^ 2 * g1 * h0 ^ 9 -
              (349440 : K[X]) * a6 * g1 ^ 3 * h0 ^ 9 +
              (74256 : K[X]) * g1 ^ 5 * h0 ^ 9)) =
      Polynomial.C κ₇ * h0 ^ 24 := by
  have hJ' := hJ
  simp only [alignedEighthDefect810, hHsq, hg] at hJ'
  apply mul_left_cancel₀ (pow_ne_zero 32 hh0)
  linear_combination hJ' -
    h0 ^ 32 *
      ((229376 : K[X]) * a3 * h0 ^ 12 -
        (286720 : K[X]) * a4 * g1 * h0 ^ 8 -
        (286720 : K[X]) * a5 * a6 * h0 ^ 4 +
        (322560 : K[X]) * a5 * g1 ^ 2 * h0 ^ 4 +
        (322560 : K[X]) * a6 ^ 2 * g1 -
        (349440 : K[X]) * a6 * g1 ^ 3 +
        (74256 : K[X]) * g1 ^ 5) * hq7

/-! ## Nonsquare chamber -/

set_option maxHeartbeats 1600000000 in
/-- Peeling `H¹⁶` from `J = κ₇ H²⁸` on `p₇ = H² g₂` and consuming the
previous factored quotient (`128 q₇ H` solved) with the mate
`229376 p₃ H⁶ - 286720 p₄ g₂ H⁴ - 286720 p₅ p₆ H² + 322560 p₅ g₂² H²
+ 322560 p₆² g₂ - 349440 p₆ g₂³ + 74256 g₂⁵`, leaves the cleared
eighth row of the nonsquare chamber (the factored transport form is an
exact rearrangement, carried by the chamber dichotomy).  The even
exponent forces nothing: `κ₇` is preserved, not cleared. -/
theorem alignedNonsquareEighth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₇ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hJ : alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4 b5
        b6 b7 κ =
      Polynomial.C κ₇ * H ^ 28)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    ((41943040 : K[X]) * a0 * H ^ 12 -
        (33554432 : K[X]) * b2 * H ^ 11 -
        (5242880 : K[X]) * a1 * g2 * H ^ 10 +
        (12582912 : K[X]) * b3 * g2 * H ^ 9 -
        (10485760 : K[X]) * a2 * a6 * H ^ 8 +
        (5242880 : K[X]) * a2 * g2 ^ 2 * H ^ 8 -
        (15728640 : K[X]) * a3 * a5 * H ^ 8 -
        (26214400 : K[X]) * a4 ^ 2 * H ^ 8 +
        (25165824 : K[X]) * a4 * b6 * H ^ 7 +
        (20971520 : K[X]) * a5 * b5 * H ^ 7 +
        (16777216 : K[X]) * b4 * a6 * H ^ 7 -
        (10485760 : K[X]) * b4 * g2 ^ 2 * H ^ 7 +
        (15728640 : K[X]) * a3 * a6 * g2 * H ^ 6 -
        (5242880 : K[X]) * a3 * g2 ^ 3 * H ^ 6 +
        (13107200 : K[X]) * a4 * a5 * g2 * H ^ 6 -
        (31457280 : K[X]) * a5 * b6 * g2 * H ^ 5 -
        (26214400 : K[X]) * b5 * a6 * g2 * H ^ 5 +
        (9830400 : K[X]) * b5 * g2 ^ 3 * H ^ 5 +
        (6553600 : K[X]) * a4 * a6 ^ 2 * H ^ 4 -
        (18022400 : K[X]) * a4 * a6 * g2 ^ 2 * H ^ 4 +
        (4812800 : K[X]) * a4 * g2 ^ 4 * H ^ 4 -
        (13107200 : K[X]) * a5 ^ 2 * a6 * H ^ 4 +
        (18841600 : K[X]) * a5 ^ 2 * g2 ^ 2 * H ^ 4 -
        (15728640 : K[X]) * b6 * a6 ^ 2 * H ^ 3 +
        (35389440 : K[X]) * b6 * a6 * g2 ^ 2 * H ^ 3 -
        (9584640 : K[X]) * b6 * g2 ^ 4 * H ^ 3 +
        (32768000 : K[X]) * a5 * a6 ^ 2 * g2 * H ^ 2 -
        (34816000 : K[X]) * a5 * a6 * g2 ^ 3 * H ^ 2 +
        (7372800 : K[X]) * a5 * g2 ^ 5 * H ^ 2 +
        (3686400 : K[X]) * a6 ^ 4 -
        (16588800 : K[X]) * a6 ^ 3 * g2 ^ 2 +
        (14860800 : K[X]) * a6 ^ 2 * g2 ^ 4 -
        (4617600 : K[X]) * a6 * g2 ^ 6 +
        (464100 : K[X]) * g2 ^ 8 +
          Polynomial.C κ *
            ((1048576 : K[X]) * a2 * H ^ 11 -
              (393216 : K[X]) * a3 * g2 * H ^ 9 -
              (1310720 : K[X]) * a4 * a6 * H ^ 7 +
              (327680 : K[X]) * a4 * g2 ^ 2 * H ^ 7 -
              (655360 : K[X]) * a5 ^ 2 * H ^ 7 +
              (1802240 : K[X]) * a5 * a6 * g2 * H ^ 5 -
              (307200 : K[X]) * a5 * g2 ^ 3 * H ^ 5 +
              (491520 : K[X]) * a6 ^ 3 * H ^ 3 -
              (1105920 : K[X]) * a6 ^ 2 * g2 ^ 2 * H ^ 3 +
              (299520 : K[X]) * a6 * g2 ^ 4 * H ^ 3)) =
      Polynomial.C κ₇ * H ^ 12 := by
  have hJ' := hJ
  simp only [alignedEighthDefect810, hg2] at hJ'
  apply mul_left_cancel₀ (pow_ne_zero 16 hH)
  linear_combination hJ' -
    H ^ 16 *
      ((229376 : K[X]) * a3 * H ^ 6 -
        (286720 : K[X]) * a4 * g2 * H ^ 4 -
        (286720 : K[X]) * a5 * a6 * H ^ 2 +
        (322560 : K[X]) * a5 * g2 ^ 2 * H ^ 2 +
        (322560 : K[X]) * a6 ^ 2 * g2 -
        (349440 : K[X]) * a6 * g2 ^ 3 +
        (74256 : K[X]) * g2 ^ 5) * hfac

/-! ## Source-facing eighth-row packets -/

/-- Source-facing weight-fifty-six integral of a normalized aligned
scale-two `(8,10)` source: the degree-`9` row is consumed into
`J = κ₇ H²⁸` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedEighthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ : K),
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
          Polynomial.C κ₇ * H ^ 28 := by
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
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, aligned_q9_solved_810 haligned, hM,
    hE4, hF2, hG, hI2, hJ⟩

/-- Exact square-chamber eighth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`9`
row gives the cleared eighth row (with `p₀` at `h₀²⁴` and `q₂` at
`h₀²²`) against the preserved `κ₇`, the carried root collapse
`g₁ = p₆ = 0`, and the carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedEighthFace_squareChamber_packet
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
    ∃ (κ μ κ₇ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ((41943040 : K[X]) * p.coeff 0 * h0 ^ 24 -
            (33554432 : K[X]) * q.coeff 2 * h0 ^ 22 -
            (5242880 : K[X]) * p.coeff 1 * g1 * h0 ^ 20 +
            (12582912 : K[X]) * q.coeff 3 * g1 * h0 ^ 18 -
            (10485760 : K[X]) * p.coeff 2 * p.coeff 6 * h0 ^ 16 +
            (5242880 : K[X]) * p.coeff 2 * g1 ^ 2 * h0 ^ 16 -
            (15728640 : K[X]) * p.coeff 3 * p.coeff 5 * h0 ^ 16 -
            (26214400 : K[X]) * p.coeff 4 ^ 2 * h0 ^ 16 +
            (25165824 : K[X]) * p.coeff 4 * q.coeff 6 * h0 ^ 14 +
            (20971520 : K[X]) * p.coeff 5 * q.coeff 5 * h0 ^ 14 +
            (16777216 : K[X]) * q.coeff 4 * p.coeff 6 * h0 ^ 14 -
            (10485760 : K[X]) * q.coeff 4 * g1 ^ 2 * h0 ^ 14 +
            (15728640 : K[X]) * p.coeff 3 * p.coeff 6 * g1 * h0 ^ 12 -
            (5242880 : K[X]) * p.coeff 3 * g1 ^ 3 * h0 ^ 12 +
            (13107200 : K[X]) * p.coeff 4 * p.coeff 5 * g1 * h0 ^ 12 -
            (31457280 : K[X]) * p.coeff 5 * q.coeff 6 * g1 * h0 ^ 10 -
            (26214400 : K[X]) * q.coeff 5 * p.coeff 6 * g1 * h0 ^ 10 +
            (9830400 : K[X]) * q.coeff 5 * g1 ^ 3 * h0 ^ 10 +
            (6553600 : K[X]) * p.coeff 4 * p.coeff 6 ^ 2 * h0 ^ 8 -
            (18022400 : K[X]) * p.coeff 4 * p.coeff 6 * g1 ^ 2 * h0 ^ 8 +
            (4812800 : K[X]) * p.coeff 4 * g1 ^ 4 * h0 ^ 8 -
            (13107200 : K[X]) * p.coeff 5 ^ 2 * p.coeff 6 * h0 ^ 8 +
            (18841600 : K[X]) * p.coeff 5 ^ 2 * g1 ^ 2 * h0 ^ 8 -
            (15728640 : K[X]) * q.coeff 6 * p.coeff 6 ^ 2 * h0 ^ 6 +
            (35389440 : K[X]) * q.coeff 6 * p.coeff 6 * g1 ^ 2 * h0 ^ 6 -
            (9584640 : K[X]) * q.coeff 6 * g1 ^ 4 * h0 ^ 6 +
            (32768000 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * g1 * h0 ^ 4 -
            (34816000 : K[X]) * p.coeff 5 * p.coeff 6 * g1 ^ 3 * h0 ^ 4 +
            (7372800 : K[X]) * p.coeff 5 * g1 ^ 5 * h0 ^ 4 +
            (3686400 : K[X]) * p.coeff 6 ^ 4 -
            (16588800 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 2 +
            (14860800 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 4 -
            (4617600 : K[X]) * p.coeff 6 * g1 ^ 6 +
            (464100 : K[X]) * g1 ^ 8 +
              Polynomial.C κ *
                ((1048576 : K[X]) * p.coeff 2 * h0 ^ 22 -
                  (393216 : K[X]) * p.coeff 3 * g1 * h0 ^ 18 -
                  (1310720 : K[X]) * p.coeff 4 * p.coeff 6 * h0 ^ 14 +
                  (327680 : K[X]) * p.coeff 4 * g1 ^ 2 * h0 ^ 14 -
                  (655360 : K[X]) * p.coeff 5 ^ 2 * h0 ^ 14 +
                  (1802240 : K[X]) * p.coeff 5 * p.coeff 6 * g1 * h0 ^ 10 -
                  (307200 : K[X]) * p.coeff 5 * g1 ^ 3 * h0 ^ 10 +
                  (491520 : K[X]) * p.coeff 6 ^ 3 * h0 ^ 6 -
                  (1105920 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 2 * h0 ^ 6 +
                  (299520 : K[X]) * p.coeff 6 * g1 ^ 4 * h0 ^ 6) -
              Polynomial.C μ *
                ((229376 : K[X]) * p.coeff 3 * h0 ^ 21 -
                  (286720 : K[X]) * p.coeff 4 * g1 * h0 ^ 17 -
                  (286720 : K[X]) * p.coeff 5 * p.coeff 6 * h0 ^ 13 +
                  (322560 : K[X]) * p.coeff 5 * g1 ^ 2 * h0 ^ 13 +
                  (322560 : K[X]) * p.coeff 6 ^ 2 * g1 * h0 ^ 9 -
                  (349440 : K[X]) * p.coeff 6 * g1 ^ 3 * h0 ^ 9 +
                  (74256 : K[X]) * g1 ^ 5 * h0 ^ 9)) =
          Polynomial.C κ₇ * h0 ^ 24 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 28 := by
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
  obtain ⟨κ₇, hJrel⟩ :=
    alignedEighthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hsolved8 :=
    alignedSquareEighth_solved_810 hh0 hHsq hp7 hJrel hcore
  exact ⟨κ, μ, κ₇, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hsolved8,
    hcollapse, hdvdg1, hdvdp6, hJrel⟩

/-- Exact nonsquare-chamber eighth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂` and the previous
packet, the consumed degree-`9` row gives the cleared eighth row (with
`p₀` at `H¹²` and `q₂` at `H¹¹`) against the preserved `κ₇`, the
carried root collapse `g₂ = p₆ = 0` at every (simple) root of the
core, and the carried descents `H ∣ g₂`, `H ∣ p₆`.  Unlike the odd
rows, the even exponent forces nothing: `κ₇` is not cleared. -/
theorem normalized810ScaleTwo_alignedEighthFace_nonsquareChamber_packet
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
    ∃ (κ κ₇ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        ((41943040 : K[X]) * p.coeff 0 * H ^ 12 -
            (33554432 : K[X]) * q.coeff 2 * H ^ 11 -
            (5242880 : K[X]) * p.coeff 1 * g2 * H ^ 10 +
            (12582912 : K[X]) * q.coeff 3 * g2 * H ^ 9 -
            (10485760 : K[X]) * p.coeff 2 * p.coeff 6 * H ^ 8 +
            (5242880 : K[X]) * p.coeff 2 * g2 ^ 2 * H ^ 8 -
            (15728640 : K[X]) * p.coeff 3 * p.coeff 5 * H ^ 8 -
            (26214400 : K[X]) * p.coeff 4 ^ 2 * H ^ 8 +
            (25165824 : K[X]) * p.coeff 4 * q.coeff 6 * H ^ 7 +
            (20971520 : K[X]) * p.coeff 5 * q.coeff 5 * H ^ 7 +
            (16777216 : K[X]) * q.coeff 4 * p.coeff 6 * H ^ 7 -
            (10485760 : K[X]) * q.coeff 4 * g2 ^ 2 * H ^ 7 +
            (15728640 : K[X]) * p.coeff 3 * p.coeff 6 * g2 * H ^ 6 -
            (5242880 : K[X]) * p.coeff 3 * g2 ^ 3 * H ^ 6 +
            (13107200 : K[X]) * p.coeff 4 * p.coeff 5 * g2 * H ^ 6 -
            (31457280 : K[X]) * p.coeff 5 * q.coeff 6 * g2 * H ^ 5 -
            (26214400 : K[X]) * q.coeff 5 * p.coeff 6 * g2 * H ^ 5 +
            (9830400 : K[X]) * q.coeff 5 * g2 ^ 3 * H ^ 5 +
            (6553600 : K[X]) * p.coeff 4 * p.coeff 6 ^ 2 * H ^ 4 -
            (18022400 : K[X]) * p.coeff 4 * p.coeff 6 * g2 ^ 2 * H ^ 4 +
            (4812800 : K[X]) * p.coeff 4 * g2 ^ 4 * H ^ 4 -
            (13107200 : K[X]) * p.coeff 5 ^ 2 * p.coeff 6 * H ^ 4 +
            (18841600 : K[X]) * p.coeff 5 ^ 2 * g2 ^ 2 * H ^ 4 -
            (15728640 : K[X]) * q.coeff 6 * p.coeff 6 ^ 2 * H ^ 3 +
            (35389440 : K[X]) * q.coeff 6 * p.coeff 6 * g2 ^ 2 * H ^ 3 -
            (9584640 : K[X]) * q.coeff 6 * g2 ^ 4 * H ^ 3 +
            (32768000 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * g2 * H ^ 2 -
            (34816000 : K[X]) * p.coeff 5 * p.coeff 6 * g2 ^ 3 * H ^ 2 +
            (7372800 : K[X]) * p.coeff 5 * g2 ^ 5 * H ^ 2 +
            (3686400 : K[X]) * p.coeff 6 ^ 4 -
            (16588800 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 2 +
            (14860800 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 4 -
            (4617600 : K[X]) * p.coeff 6 * g2 ^ 6 +
            (464100 : K[X]) * g2 ^ 8 +
              Polynomial.C κ *
                ((1048576 : K[X]) * p.coeff 2 * H ^ 11 -
                  (393216 : K[X]) * p.coeff 3 * g2 * H ^ 9 -
                  (1310720 : K[X]) * p.coeff 4 * p.coeff 6 * H ^ 7 +
                  (327680 : K[X]) * p.coeff 4 * g2 ^ 2 * H ^ 7 -
                  (655360 : K[X]) * p.coeff 5 ^ 2 * H ^ 7 +
                  (1802240 : K[X]) * p.coeff 5 * p.coeff 6 * g2 * H ^ 5 -
                  (307200 : K[X]) * p.coeff 5 * g2 ^ 3 * H ^ 5 +
                  (491520 : K[X]) * p.coeff 6 ^ 3 * H ^ 3 -
                  (1105920 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 2 * H ^ 3 +
                  (299520 : K[X]) * p.coeff 6 * g2 ^ 4 * H ^ 3)) =
          Polynomial.C κ₇ * H ^ 12 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 28 := by
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
  obtain ⟨κ₇, hJrel⟩ :=
    alignedEighthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hclear8 :=
    alignedNonsquareEighth_solved_810 hH hg2 hJrel hfac
  exact ⟨κ, κ₇, g2, hg2, by rw [hq9, hg2]; ring, hclear8,
    hcollapse, hdvdg2, hdvdp6, hJrel⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`9`
aligned row, carrying the factored transport of the octic block.
Neither chamber is excluded, the constants `κ`, `μ`, `κ₇` are
preserved (nothing is forced by the even exponent), and no closure is
claimed. -/
theorem normalized810ScaleTwo_alignedEighthFace_chamberDichotomy
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
      ∃ (κ μ κ₇ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (300 : K[X]) *
              ((1547 : K[X]) * g1 ^ 8 -
                (15392 : K[X]) * p.coeff 6 * g1 ^ 6 +
                (49536 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 4 -
                (55296 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 2 +
                (12288 : K[X]) * p.coeff 6 ^ 4) =
            h0 ^ 4 *
              (Polynomial.C κ₇ * h0 ^ 20 -
                ((41943040 : K[X]) * p.coeff 0 * h0 ^ 20 -
                (33554432 : K[X]) * q.coeff 2 * h0 ^ 18 -
                (5242880 : K[X]) * p.coeff 1 * g1 * h0 ^ 16 +
                (12582912 : K[X]) * q.coeff 3 * g1 * h0 ^ 14 -
                (10485760 : K[X]) * p.coeff 2 * p.coeff 6 * h0 ^ 12 +
                (5242880 : K[X]) * p.coeff 2 * g1 ^ 2 * h0 ^ 12 -
                (15728640 : K[X]) * p.coeff 3 * p.coeff 5 * h0 ^ 12 -
                (26214400 : K[X]) * p.coeff 4 ^ 2 * h0 ^ 12 +
                (25165824 : K[X]) * p.coeff 4 * q.coeff 6 * h0 ^ 10 +
                (20971520 : K[X]) * p.coeff 5 * q.coeff 5 * h0 ^ 10 +
                (16777216 : K[X]) * q.coeff 4 * p.coeff 6 * h0 ^ 10 -
                (10485760 : K[X]) * q.coeff 4 * g1 ^ 2 * h0 ^ 10 +
                (15728640 : K[X]) * p.coeff 3 * p.coeff 6 * g1 * h0 ^ 8 -
                (5242880 : K[X]) * p.coeff 3 * g1 ^ 3 * h0 ^ 8 +
                (13107200 : K[X]) * p.coeff 4 * p.coeff 5 * g1 * h0 ^ 8 -
                (31457280 : K[X]) * p.coeff 5 * q.coeff 6 * g1 * h0 ^ 6 -
                (26214400 : K[X]) * q.coeff 5 * p.coeff 6 * g1 * h0 ^ 6 +
                (9830400 : K[X]) * q.coeff 5 * g1 ^ 3 * h0 ^ 6 +
                (6553600 : K[X]) * p.coeff 4 * p.coeff 6 ^ 2 * h0 ^ 4 -
                (18022400 : K[X]) * p.coeff 4 * p.coeff 6 * g1 ^ 2 * h0 ^ 4 +
                (4812800 : K[X]) * p.coeff 4 * g1 ^ 4 * h0 ^ 4 -
                (13107200 : K[X]) * p.coeff 5 ^ 2 * p.coeff 6 * h0 ^ 4 +
                (18841600 : K[X]) * p.coeff 5 ^ 2 * g1 ^ 2 * h0 ^ 4 -
                (15728640 : K[X]) * q.coeff 6 * p.coeff 6 ^ 2 * h0 ^ 2 +
                (35389440 : K[X]) * q.coeff 6 * p.coeff 6 * g1 ^ 2 * h0 ^ 2 -
                (9584640 : K[X]) * q.coeff 6 * g1 ^ 4 * h0 ^ 2 +
                (32768000 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * g1 -
                (34816000 : K[X]) * p.coeff 5 * p.coeff 6 * g1 ^ 3 +
                (7372800 : K[X]) * p.coeff 5 * g1 ^ 5 +
                  Polynomial.C κ *
                    ((1048576 : K[X]) * p.coeff 2 * h0 ^ 18 -
                      (393216 : K[X]) * p.coeff 3 * g1 * h0 ^ 14 -
                      (1310720 : K[X]) * p.coeff 4 * p.coeff 6 * h0 ^ 10 +
                      (327680 : K[X]) * p.coeff 4 * g1 ^ 2 * h0 ^ 10 -
                      (655360 : K[X]) * p.coeff 5 ^ 2 * h0 ^ 10 +
                      (1802240 : K[X]) * p.coeff 5 * p.coeff 6 * g1 * h0 ^ 6 -
                      (307200 : K[X]) * p.coeff 5 * g1 ^ 3 * h0 ^ 6 +
                      (491520 : K[X]) * p.coeff 6 ^ 3 * h0 ^ 2 -
                      (1105920 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 2 * h0 ^ 2 +
                      (299520 : K[X]) * p.coeff 6 * g1 ^ 4 * h0 ^ 2) -
                  Polynomial.C μ *
                    ((229376 : K[X]) * p.coeff 3 * h0 ^ 17 -
                      (286720 : K[X]) * p.coeff 4 * g1 * h0 ^ 13 -
                      (286720 : K[X]) * p.coeff 5 * p.coeff 6 * h0 ^ 9 +
                      (322560 : K[X]) * p.coeff 5 * g1 ^ 2 * h0 ^ 9 +
                      (322560 : K[X]) * p.coeff 6 ^ 2 * g1 * h0 ^ 5 -
                      (349440 : K[X]) * p.coeff 6 * g1 ^ 3 * h0 ^ 5 +
                      (74256 : K[X]) * g1 ^ 5 * h0 ^ 5))) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₇ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (300 : K[X]) *
              ((1547 : K[X]) * g2 ^ 8 -
                (15392 : K[X]) * p.coeff 6 * g2 ^ 6 +
                (49536 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 4 -
                (55296 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 2 +
                (12288 : K[X]) * p.coeff 6 ^ 4) =
            H ^ 2 *
              (Polynomial.C κ₇ * H ^ 10 -
                ((41943040 : K[X]) * p.coeff 0 * H ^ 10 -
                (33554432 : K[X]) * q.coeff 2 * H ^ 9 -
                (5242880 : K[X]) * p.coeff 1 * g2 * H ^ 8 +
                (12582912 : K[X]) * q.coeff 3 * g2 * H ^ 7 -
                (10485760 : K[X]) * p.coeff 2 * p.coeff 6 * H ^ 6 +
                (5242880 : K[X]) * p.coeff 2 * g2 ^ 2 * H ^ 6 -
                (15728640 : K[X]) * p.coeff 3 * p.coeff 5 * H ^ 6 -
                (26214400 : K[X]) * p.coeff 4 ^ 2 * H ^ 6 +
                (25165824 : K[X]) * p.coeff 4 * q.coeff 6 * H ^ 5 +
                (20971520 : K[X]) * p.coeff 5 * q.coeff 5 * H ^ 5 +
                (16777216 : K[X]) * q.coeff 4 * p.coeff 6 * H ^ 5 -
                (10485760 : K[X]) * q.coeff 4 * g2 ^ 2 * H ^ 5 +
                (15728640 : K[X]) * p.coeff 3 * p.coeff 6 * g2 * H ^ 4 -
                (5242880 : K[X]) * p.coeff 3 * g2 ^ 3 * H ^ 4 +
                (13107200 : K[X]) * p.coeff 4 * p.coeff 5 * g2 * H ^ 4 -
                (31457280 : K[X]) * p.coeff 5 * q.coeff 6 * g2 * H ^ 3 -
                (26214400 : K[X]) * q.coeff 5 * p.coeff 6 * g2 * H ^ 3 +
                (9830400 : K[X]) * q.coeff 5 * g2 ^ 3 * H ^ 3 +
                (6553600 : K[X]) * p.coeff 4 * p.coeff 6 ^ 2 * H ^ 2 -
                (18022400 : K[X]) * p.coeff 4 * p.coeff 6 * g2 ^ 2 * H ^ 2 +
                (4812800 : K[X]) * p.coeff 4 * g2 ^ 4 * H ^ 2 -
                (13107200 : K[X]) * p.coeff 5 ^ 2 * p.coeff 6 * H ^ 2 +
                (18841600 : K[X]) * p.coeff 5 ^ 2 * g2 ^ 2 * H ^ 2 -
                (15728640 : K[X]) * q.coeff 6 * p.coeff 6 ^ 2 * H +
                (35389440 : K[X]) * q.coeff 6 * p.coeff 6 * g2 ^ 2 * H -
                (9584640 : K[X]) * q.coeff 6 * g2 ^ 4 * H +
                (32768000 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * g2 -
                (34816000 : K[X]) * p.coeff 5 * p.coeff 6 * g2 ^ 3 +
                (7372800 : K[X]) * p.coeff 5 * g2 ^ 5 +
                  Polynomial.C κ *
                    ((1048576 : K[X]) * p.coeff 2 * H ^ 9 -
                      (393216 : K[X]) * p.coeff 3 * g2 * H ^ 7 -
                      (1310720 : K[X]) * p.coeff 4 * p.coeff 6 * H ^ 5 +
                      (327680 : K[X]) * p.coeff 4 * g2 ^ 2 * H ^ 5 -
                      (655360 : K[X]) * p.coeff 5 ^ 2 * H ^ 5 +
                      (1802240 : K[X]) * p.coeff 5 * p.coeff 6 * g2 * H ^ 3 -
                      (307200 : K[X]) * p.coeff 5 * g2 ^ 3 * H ^ 3 +
                      (491520 : K[X]) * p.coeff 6 ^ 3 * H -
                      (1105920 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 2 * H +
                      (299520 : K[X]) * p.coeff 6 * g2 ^ 4 * H))) ∧
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
      normalized810ScaleTwo_alignedEighthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₇, g1, hp7, hq9, hsolved8,
      hcollapse, hdvdg1, hdvdp6, _hJrel⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₇, g1, hp7, hq9,
      by linear_combination hsolved8, hcollapse, hdvdg1, hdvdp6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedEighthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₇, g2, hp7, hq9, hclear8, hcollapse,
      hdvdg2, hdvdp6, _hJrel⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₇, g2, hp7, hq9,
      by linear_combination hclear8, hcollapse, hdvdg2, hdvdp6⟩

/-- Chamber-independent root jet after the consumed degree-`9` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its octic content is absorbed by the
degree-`13` collapse (`alignedEighth_rootOctic_absorbed_810`) — and
the new coefficients `p₀, q₂` are tied into the cleared eighth row
instead of being killed. -/
theorem normalized810ScaleTwo_alignedEighthFace_rootJet
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
  normalized810ScaleTwo_alignedSeventhFace_rootJet hsource haligned

#print axioms alignedEighthCoefficientJacobianRow_810
#print axioms alignedEighthDefect_weightedDerivative_identity_810
#print axioms alignedEighthDefectRow_eq_zero_810
#print axioms alignedEighthDefectPowerRelation_810
#print axioms alignedEighth_factored_rootOctic_810
#print axioms alignedEighth_rootOctic_absorbed_810
#print axioms alignedSquareEighth_solved_810
#print axioms alignedNonsquareEighth_solved_810
#print axioms normalized810ScaleTwo_alignedEighthFace_packet
#print axioms normalized810ScaleTwo_alignedEighthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedEighthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedEighthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedEighthFace_rootJet

end Max11DegreeRoutes
