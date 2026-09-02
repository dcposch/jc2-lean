import Fable610ScaleTwoAlignedSixthFaceScratch

/-! # Seventh aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedSixthFaceScratch` consumed the degree-`9`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
chamber-free weight-fifteen integral `G = κ₅ H¹⁵`, with the sextic tie
`58320 p₃² - 38880 p₃ f₂ w₁ - 6480 f₂³ + 8640 p₃ w₁³ + 12960 f₂² w₁²
- 5040 f₂ w₁⁴ + 560 w₁⁶ = h₀² s` (nonsquare: `= H t`) whose
discriminant `2²·3⁷ (3 f₂ - w₁²)³` is not a square in general.  This
file consumes the next unused aligned row, the degree-`8` Jacobian
coefficient — the first row that sees `q₃`.

At the source level, modulo the face and the consumed degree-`13`
relation `C = 9 q₈ H - 15 p₄ H³ - 5 p₅² - κ H⁵ = 0` and the consumed
degree-`12`, `11`, `10`, `9` rows, the degree-`8` row is the weighted
derivative of the cleared seventh defect

`I = 2799360 (p₀ p₅ + p₁ p₄ + p₂ p₃) H¹⁵ - 2519424 q₃ H¹⁶
  - 466560 p₁ p₅² H¹² - 933120 p₂ p₄ p₅ H¹² - 466560 p₃² p₅ H¹²
  - 466560 p₃ p₄² H¹² + 207360 p₂ p₅³ H⁹ + 622080 p₃ p₄ p₅² H⁹
  + 207360 p₄³ p₅ H⁹ - 120960 p₃ p₅⁴ H⁶ - 241920 p₄² p₅³ H⁶
  + 80640 p₄ p₅⁵ H³ - 8320 p₅⁷
  + κ (373248 p₁ H¹⁷ + 124416 p₂ p₅ H¹⁴ + 124416 p₃ p₄ H¹⁴
       - 41472 p₃ p₅² H¹¹ - 41472 p₄² p₅ H¹¹ + 23040 p₄ p₅³ H⁸
       - 3072 p₅⁵ H⁵)
  - (36288 p₂ H⁹ + 6048 p₃ p₅ H⁶ + 3024 p₄² H⁶ - 2520 p₄ p₅² H³
     + 385 p₅⁴) D - 5184 p₃ H⁶ E - (360 p₄ H³ - 30 p₅²) F - 16 p₅ G`,

kept in factored form through the third, fourth, fifth, and sixth
defects, via the exact multiplier identity

`839808 H¹⁴ · row₈[p₆ = H³] = (2 H I' - 35 I H')
  - 2519424 H¹⁴ p₀' N
  + (746496 H¹³ p₁' + 93312 H¹² p₁ H') C - 93312 H¹³ p₁ C'
  + (46656 p₂ H⁹ + 54432 p₃ p₅ H⁶ + 27216 p₄² H⁶ + 4536 p₄ p₅² H³
     - 315 p₅⁴)(2 H D' - 15 D H')
  + (15552 p₃ H⁶ + 15552 p₄ p₅ H³)(H E' - 10 E H')
  + (648 p₄ H³ + 270 p₅²)(2 H F' - 25 F H') + 72 p₅ (H G' - 15 G H')`

(the row has no `q₉'` term, so the `N`-correction needs no `N'`).  On
the aligned face every correction vanishes, so `2 H I' = 35 I H'` and
the squared weight-thirty-five first integral `I² = κ₆ H³⁵` holds for
a preserved constant `κ₆`.  The odd exponent splits on the chambers:

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `E = κ₃ H¹⁰`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`): the
  integral has a polynomial square root `I = ν₂ h₀³⁵` with `ν₂² = κ₆`.
  Cancelling `h₀²⁸` leaves the chamber core whose `h₀`-free part is
  `-640 (729 p₃² w₁ + 729 p₃ f₂² - 972 p₃ f₂ w₁² + 189 p₃ w₁⁴
  - 324 f₂³ w₁ + 378 f₂² w₁³ - 126 f₂ w₁⁵ + 13 w₁⁷)`.  At the root of
  `h₀` this septic combines with the sixth-face sextic tie through the
  two factorizations (`α = 27 p₃ - w₁³`, `β = 3 f₂ - w₁²`)
  `septic = w₁·sextic + 3 β² (α - 3 β w₁)` and
  `sextic = (α - 3 β w₁)² - 3 β³`, which force `β(a) = 0` AND
  `α(a) = 0` in every case: the sextic tie on `p₃` is RESOLVED into
  the exact pins `3 f₂(a) = w₁(a)²` and `27 p₃(a) = w₁(a)³`.  The
  linear-root transfer gives the NEW divisibilities
  `3 f₂ - w₁² = h₀ e₁` and `27 p₃ - w₁³ = h₀ e₂`, the sixth-face
  quotient is refined to `s = 80 (e₂ - 3 e₁ w₁)² - 240 h₀ e₁³`, and
  cancelling `h₀²` once more yields the twice-peeled row with `q₃`
  tied at `h₀²` and `h₀`-free head `-640 w₁ (e₂ - 3 e₁ w₁)²`, leaving
  at the root the honest residual branch
  `w₁(a) = 0 ∨ e₂(a) = 3 e₁(a) w₁(a)`.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `E = κ₃ H¹⁰`,
  `G = κ₅ H¹⁵`): the odd exponent forces `κ₆ = 0` and `I = 0`
  identically; cancelling `H¹⁴` leaves the core whose `H`-free part is
  the same septic block, so the pins hold at BOTH simple roots and
  transfer to the divisibilities `3 f - g₁² = H t₁`,
  `27 p₃ - g₁³ = H t₂`; the sixth-face quotient itself becomes
  divisible, `t = H (80 (t₂ - 3 t₁ g₁)² - 240 H t₁³)`, and `q₃` is
  solved OUTRIGHT with the honest inhomogeneous root relation
  `2519424 q₃(a) = 466560 p₁ g₁² - 640 g₁ (t₂ - 3 t₁ g₁)²
  + 103680 p₂ t₂ - 311040 p₂ t₁ g₁ + κ·124416 p₂ g₁ - κ₃·192 g₁³`
  at each root.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, `dvd_of_sq_dvd_sq_poly`,
and `linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `g₁ = 0`, `f = 0`, `t₁ = 0`,
`t₂ = 0`, `s = 0`, `t = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `ν = 0`,
`κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`) are not excluded, and the constants `κ`,
`κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²` are preserved where not
forced.  The next unused Keller row on the aligned face is the
degree-`7` Jacobian coefficient, the first row that sees `q₂` (pairs
`(0,8), (1,7), (2,6), (3,5), (4,4), (5,3), (6,2)`; expected weight-`20`
defect, even exponent, chamber-free like `E` and `G`).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`8` Keller coefficient on the aligned face -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`8` Jacobian coefficient, the first
aligned row that sees `q₃`. -/
theorem alignedSeventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        p.coeff 1 * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1),
        (8, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC2]
  linear_combination hcoeff

/-! ## Aligned seventh defect -/

/-- Cleared seventh defect of the degree-`8` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, and the sixth defect `G`.  On the aligned face
its square is a polynomial first integral of weight thirty-five. -/
def alignedSeventhDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (2799360 : K[X]) * a0 * a5 * H ^ 15 +
    (2799360 : K[X]) * a1 * a4 * H ^ 15 +
    (2799360 : K[X]) * a2 * a3 * H ^ 15 -
    (2519424 : K[X]) * b3 * H ^ 16 -
    (466560 : K[X]) * a1 * a5 ^ 2 * H ^ 12 -
    (933120 : K[X]) * a2 * a4 * a5 * H ^ 12 -
    (466560 : K[X]) * a3 ^ 2 * a5 * H ^ 12 -
    (466560 : K[X]) * a3 * a4 ^ 2 * H ^ 12 +
    (207360 : K[X]) * a2 * a5 ^ 3 * H ^ 9 +
    (622080 : K[X]) * a3 * a4 * a5 ^ 2 * H ^ 9 +
    (207360 : K[X]) * a4 ^ 3 * a5 * H ^ 9 -
    (120960 : K[X]) * a3 * a5 ^ 4 * H ^ 6 -
    (241920 : K[X]) * a4 ^ 2 * a5 ^ 3 * H ^ 6 +
    (80640 : K[X]) * a4 * a5 ^ 5 * H ^ 3 - (8320 : K[X]) * a5 ^ 7 +
    Polynomial.C κ *
      ((373248 : K[X]) * a1 * H ^ 17 +
        (124416 : K[X]) * a2 * a5 * H ^ 14 +
        (124416 : K[X]) * a3 * a4 * H ^ 14 -
        (41472 : K[X]) * a3 * a5 ^ 2 * H ^ 11 -
        (41472 : K[X]) * a4 ^ 2 * a5 * H ^ 11 +
        (23040 : K[X]) * a4 * a5 ^ 3 * H ^ 8 -
        (3072 : K[X]) * a5 ^ 5 * H ^ 5) -
    ((36288 : K[X]) * a2 * H ^ 9 + (6048 : K[X]) * a3 * a5 * H ^ 6 +
        (3024 : K[X]) * a4 ^ 2 * H ^ 6 -
        (2520 : K[X]) * a4 * a5 ^ 2 * H ^ 3 +
        (385 : K[X]) * a5 ^ 4) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (5184 : K[X]) * a3 * H ^ 6 *
      alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ -
    ((360 : K[X]) * a4 * H ^ 3 - (30 : K[X]) * a5 ^ 2) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ -
    (16 : K[X]) * a5 *
      alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ

set_option maxHeartbeats 3200000000 in
/-- Exact combination of the degree-`8` Jacobian expression with the
weighted derivative of `I`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13`,
degree-`12`, degree-`11`, degree-`10`, and degree-`9` rows.  The row
has no `q₉`-derivative term, so the `N`-correction carries no `N'`. -/
theorem alignedSeventhDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (839808 : K[X]) * H ^ 14 *
        ((H ^ 3).derivative * (b3 * (3 : K[X])) +
          a5.derivative * (b4 * (4 : K[X])) +
          a4.derivative * (b5 * (5 : K[X])) +
          a3.derivative * (b6 * (6 : K[X])) +
          a2.derivative * (b7 * (7 : K[X])) +
          a1.derivative * (b8 * (8 : K[X])) +
          a0.derivative * (b9 * (9 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b3.derivative +
          (a5 * (5 : K[X])) * b4.derivative +
          (a4 * (4 : K[X])) * b5.derivative +
          (a3 * (3 : K[X])) * b6.derivative +
          (a2 * (2 : K[X])) * b7.derivative +
          a1 * b8.derivative)) =
      ((2 : K[X]) * H *
          (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
            κ).derivative -
        (35 : K[X]) *
          alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ *
          H.derivative) -
        (2519424 : K[X]) * H ^ 14 * a0.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) +
        ((746496 : K[X]) * H ^ 13 * a1.derivative +
            (93312 : K[X]) * H ^ 12 * a1 * H.derivative) *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) -
        (93312 : K[X]) * H ^ 13 * a1 *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5).derivative +
        ((46656 : K[X]) * a2 * H ^ 9 + (54432 : K[X]) * a3 * a5 * H ^ 6 +
            (27216 : K[X]) * a4 ^ 2 * H ^ 6 +
            (4536 : K[X]) * a4 * a5 ^ 2 * H ^ 3 -
            (315 : K[X]) * a5 ^ 4) *
          ((2 : K[X]) * H *
              (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
            (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
              H.derivative) +
        ((15552 : K[X]) * a3 * H ^ 6 + (15552 : K[X]) * a4 * a5 * H ^ 3) *
          (H * (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative -
            (10 : K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ *
              H.derivative) +
        ((648 : K[X]) * a4 * H ^ 3 + (270 : K[X]) * a5 ^ 2) *
          ((2 : K[X]) * H *
              (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7
                κ).derivative -
            (25 : K[X]) *
              alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ *
              H.derivative) +
        (72 : K[X]) * a5 *
          (H *
              (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7
                κ).derivative -
            (15 : K[X]) *
              alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ *
              H.derivative) := by
  simp only [alignedSeventhDefect610, alignedSixthDefect610,
    alignedFifthDefect610, alignedFourthDefect610, alignedThirdDefect610,
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

/-- On the aligned face, with the consumed degree-`13` through
degree-`9` rows, the degree-`8` row is the weighted derivative
`2 H I' - 35 I H' = 0`. -/
theorem alignedSeventhDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H *
        (alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (35 : K[X]) *
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedSeventhCoefficientJacobianRow_610 hp hq hjac
  rw [hp6] at hrow
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC2] at hrow
  have hC0 :
      (9 : K[X]) * q.coeff 8 * H - (15 : K[X]) * p.coeff 4 * H ^ 3 -
          (5 : K[X]) * p.coeff 5 ^ 2 - Polynomial.C κ * H ^ 5 = 0 := by
    have hM' :
        (9 : K[X]) * q.coeff 8 * H - (15 : K[X]) * p.coeff 4 * H ^ 3 -
            (5 : K[X]) * p.coeff 5 ^ 2 = Polynomial.C κ * H ^ 5 := by
      simpa only [alignedSecondDefect610] using hM
    linear_combination hM'
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedSeventhDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
    (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hDrow, hErow, hFrow, hGrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-thirty-five polynomial first integral of the aligned
`(6,10)` seventh defect: `I² = κ₆ H³⁵`. -/
theorem alignedSeventhDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₆ : K,
      alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₆ * H ^ 35 := by
  let I : K[X] :=
    alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
      (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * I.derivative -
        (35 : K[X]) * I * H.derivative = 0 := by
    simpa only [I] using
      alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC35 : Polynomial.C (35 : K) = (35 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (I ^ 2) (H ^ 35) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      I ^ 2 * (Polynomial.C (35 : K) * H ^ (35 - 1) * H.derivative) -
          Polynomial.C (2 : K) * I ^ (2 - 1) * I.derivative * H ^ 35 =
          I * H ^ 34 *
            (Polynomial.C (35 : K) * I * H.derivative -
              Polynomial.C (2 : K) * H * I.derivative) := by
        ring
      _ = 0 := by
        rw [hC35, hC2]
        have hfac :
            (35 : K[X]) * I * H.derivative -
              (2 : K[X]) * H * I.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 35 hH) hW

/-! ## Square chamber -/

/-- In the square chamber the weight-thirty-five integral has a
polynomial square root: `I = ν₂ h₀³⁵` with `ν₂² = κ₆`.  The constant
`ν₂` is preserved, not cleared. -/
theorem alignedSquareSeventh_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : K[X]} {κ κ₆ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hI2 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ ^ 2 =
        Polynomial.C κ₆ * H ^ 35) :
    ∃ ν₂ : K, ν₂ ^ 2 = κ₆ ∧
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
        Polynomial.C ν₂ * h0 ^ 35 := by
  set I : K[X] :=
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 35) ^ 2 ∣ I ^ 2 := by
    refine ⟨Polynomial.C κ₆, ?_⟩
    rw [hI2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₆ := by
    have h70 := hI2
    rw [hG, hHsq] at h70
    apply mul_left_cancel₀ (pow_ne_zero 70 hh0)
    linear_combination h70
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₆
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν₂, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν₂, ?_, ?_⟩
  · have hCν : Polynomial.C (ν₂ ^ 2) = Polynomial.C κ₆ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

/-- Scalar resolution of the seventh-row septic root tie against the
sixth-face sextic root tie: with `α = 27 x - z³` and `β = 3 y - z²`
the septic is `z·sextic + 3 β² (α - 3 β z)` and the sextic is
`(α - 3 β z)² - 3 β³`, so at a common root BOTH `β = 0` and `α = 0` —
the sextic tie is resolved into exact pins. -/
theorem alignedSeventhSexticResolve_610 {K : Type*} [Field K]
    [CharZero K] {x y z : K}
    (h7 : 729 * x ^ 2 * z + 729 * x * y ^ 2 - 972 * x * y * z ^ 2 +
      189 * x * z ^ 4 - 324 * y ^ 3 * z + 378 * y ^ 2 * z ^ 3 -
      126 * y * z ^ 5 + 13 * z ^ 7 = 0)
    (hB : 729 * x ^ 2 - 486 * x * y * z - 81 * y ^ 3 + 108 * x * z ^ 3 +
      162 * y ^ 2 * z ^ 2 - 63 * y * z ^ 4 + 7 * z ^ 6 = 0) :
    3 * y = z ^ 2 ∧ 27 * x = z ^ 3 := by
  have hkey :
      (3 * y - z ^ 2) ^ 2 * (27 * x - 9 * y * z + 2 * z ^ 3) = 0 := by
    linear_combination (3⁻¹ : K) * h7 - (3⁻¹ : K) * z * hB
  have hsq : (27 * x - 9 * y * z + 2 * z ^ 3) ^ 2 =
      3 * (3 * y - z ^ 2) ^ 3 := by
    linear_combination hB
  have hbz : 3 * y - z ^ 2 = 0 := by
    rcases mul_eq_zero.mp hkey with h1 | h2
    · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
    · have h3 : (3 : K) * (3 * y - z ^ 2) ^ 3 = 0 := by
        rw [← hsq, h2]
        ring
      have h4 : (3 * y - z ^ 2) ^ 3 = 0 :=
        (mul_eq_zero.mp h3).resolve_left (by norm_num : (3 : K) ≠ 0)
      exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h4
  have hax : 27 * x - 9 * y * z + 2 * z ^ 3 = 0 := by
    have h5 : (27 * x - 9 * y * z + 2 * z ^ 3) ^ 2 = 0 := by
      rw [hsq, hbz]
      ring
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h5
  exact ⟨by linear_combination hbz,
    by linear_combination hax + 3 * z * hbz⟩

/-- Descent of the consumed degree-`8` row in the square chamber: the
`h₀²⁸`-peeled core kills the septic block at the root of `h₀`, the
scalar resolution against the sixth-face sextic tie pins
`3 f₂(a) = w₁(a)²` and `27 p₃(a) = w₁(a)³`, the linear-root transfer
gives the NEW divisibilities `3 f₂ - w₁² = h₀ e₁` and
`27 p₃ - w₁³ = h₀ e₂`, the sixth-face quotient is refined to
`s = 80 (e₂ - 3 e₁ w₁)² - 240 h₀ e₁³`, and cancelling `h₀²` once more
leaves the twice-peeled row with `q₃` tied at `h₀²`. -/
theorem alignedSquareSeventh_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 s a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ ν κ₅ ν₂ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1) (hHsq : H = h0 ^ 2)
    (hp5 : a5 = h0 ^ 4 * w1) (hp4 : a4 = h0 ^ 2 * f2)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI : alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
      Polynomial.C ν₂ * h0 ^ 35)
    (htie6 : (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f2 * w1 -
        (6480 : K[X]) * f2 ^ 3 + (8640 : K[X]) * a3 * w1 ^ 3 +
        (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 - (5040 : K[X]) * f2 * w1 ^ 4 +
        (560 : K[X]) * w1 ^ 6 = h0 ^ 2 * s) :
    ∃ e1 e2 : K[X],
      (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
      (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2 ∧
      s = (80 : K[X]) * (e2 - (3 : K[X]) * e1 * w1) ^ 2 -
        (240 : K[X]) * h0 * e1 ^ 3 ∧
      (-(640 : K[X])) * w1 * (e2 - (3 : K[X]) * e1 * w1) ^ 2 +
          h0 * ((7680 : K[X]) * e1 ^ 3 * w1 -
            (1920 : K[X]) * e1 ^ 2 * e2 -
            (311040 : K[X]) * e1 * a2 * w1 + (103680 : K[X]) * e2 * a2 -
            Polynomial.C μ * ((105 : K[X]) * w1 ^ 4)) +
          h0 ^ 2 * ((466560 : K[X]) * a1 * w1 ^ 2 -
            (2519424 : K[X]) * b3 +
            Polynomial.C κ * ((1536 : K[X]) * e1 * e2 -
              (4608 : K[X]) * e1 ^ 2 * w1 + (124416 : K[X]) * a2 * w1) +
            Polynomial.C μ * ((168 : K[X]) * e1 * w1 ^ 2 -
              (224 : K[X]) * e2 * w1) -
            Polynomial.C κ₃ * ((192 : K[X]) * w1 ^ 3)) +
          h0 ^ 3 * ((933120 : K[X]) * e1 * a1 -
            Polynomial.C μ * ((336 : K[X]) * e1 ^ 2 +
              (36288 : K[X]) * a2) -
            Polynomial.C κ₃ * ((192 : K[X]) * e2) -
            Polynomial.C ν * ((90 : K[X]) * w1 ^ 2)) +
          h0 ^ 4 * ((2799360 : K[X]) * a0 * w1 +
            Polynomial.C κ * ((373248 : K[X]) * a1) -
            Polynomial.C ν * ((120 : K[X]) * e1) -
            Polynomial.C κ₅ * ((16 : K[X]) * w1)) =
        Polynomial.C ν₂ * h0 ^ 5 := by
  have hcore :
      (2799360 : K[X]) * a0 * w1 * h0 ^ 6 +
          (2799360 : K[X]) * a1 * f2 * h0 ^ 4 +
          (2799360 : K[X]) * a2 * a3 * h0 ^ 2 -
          (2519424 : K[X]) * b3 * h0 ^ 4 -
          (466560 : K[X]) * a1 * w1 ^ 2 * h0 ^ 4 -
          (933120 : K[X]) * a2 * f2 * w1 * h0 ^ 2 +
          (207360 : K[X]) * a2 * w1 ^ 3 * h0 ^ 2 -
          (466560 : K[X]) * a3 ^ 2 * w1 - (466560 : K[X]) * a3 * f2 ^ 2 +
          (622080 : K[X]) * a3 * f2 * w1 ^ 2 -
          (120960 : K[X]) * a3 * w1 ^ 4 +
          (207360 : K[X]) * f2 ^ 3 * w1 -
          (241920 : K[X]) * f2 ^ 2 * w1 ^ 3 +
          (80640 : K[X]) * f2 * w1 ^ 5 - (8320 : K[X]) * w1 ^ 7 +
          Polynomial.C κ *
            ((373248 : K[X]) * a1 * h0 ^ 6 +
              (124416 : K[X]) * a2 * w1 * h0 ^ 4 +
              (124416 : K[X]) * a3 * f2 * h0 ^ 2 -
              (41472 : K[X]) * a3 * w1 ^ 2 * h0 ^ 2 -
              (41472 : K[X]) * f2 ^ 2 * w1 * h0 ^ 2 +
              (23040 : K[X]) * f2 * w1 ^ 3 * h0 ^ 2 -
              (3072 : K[X]) * w1 ^ 5 * h0 ^ 2) -
          Polynomial.C μ *
            ((36288 : K[X]) * a2 * h0 ^ 5 +
              (6048 : K[X]) * a3 * w1 * h0 ^ 3 +
              (3024 : K[X]) * f2 ^ 2 * h0 ^ 3 -
              (2520 : K[X]) * f2 * w1 ^ 2 * h0 ^ 3 +
              (385 : K[X]) * w1 ^ 4 * h0 ^ 3) -
          Polynomial.C κ₃ * ((5184 : K[X]) * a3 * h0 ^ 4) -
          Polynomial.C ν *
            ((360 : K[X]) * f2 * h0 ^ 5 - (30 : K[X]) * w1 ^ 2 * h0 ^ 5) -
          Polynomial.C κ₅ * ((16 : K[X]) * w1 * h0 ^ 6) =
        Polynomial.C ν₂ * h0 ^ 7 := by
    have hI' := hI
    simp only [alignedSeventhDefect610] at hI'
    rw [hD, hE, hF, hG, hHsq, hp5, hp4] at hI'
    apply mul_left_cancel₀ (pow_ne_zero 28 hh0)
    linear_combination hI'
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hcore
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have hevB := congrArg (fun t : K[X] => t.eval (-(d / c))) htie6
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat] at hevB
  rw [hroot] at hevB
  have h7 : 729 * (a3.eval (-(d / c))) ^ 2 * (w1.eval (-(d / c))) +
      729 * (a3.eval (-(d / c))) * (f2.eval (-(d / c))) ^ 2 -
      972 * (a3.eval (-(d / c))) * (f2.eval (-(d / c))) *
        (w1.eval (-(d / c))) ^ 2 +
      189 * (a3.eval (-(d / c))) * (w1.eval (-(d / c))) ^ 4 -
      324 * (f2.eval (-(d / c))) ^ 3 * (w1.eval (-(d / c))) +
      378 * (f2.eval (-(d / c))) ^ 2 * (w1.eval (-(d / c))) ^ 3 -
      126 * (f2.eval (-(d / c))) * (w1.eval (-(d / c))) ^ 5 +
      13 * (w1.eval (-(d / c))) ^ 7 = 0 := by
    linear_combination (-(640⁻¹ : K)) * hev
  have hB : 729 * (a3.eval (-(d / c))) ^ 2 -
      486 * (a3.eval (-(d / c))) * (f2.eval (-(d / c))) *
        (w1.eval (-(d / c))) -
      81 * (f2.eval (-(d / c))) ^ 3 +
      108 * (a3.eval (-(d / c))) * (w1.eval (-(d / c))) ^ 3 +
      162 * (f2.eval (-(d / c))) ^ 2 * (w1.eval (-(d / c))) ^ 2 -
      63 * (f2.eval (-(d / c))) * (w1.eval (-(d / c))) ^ 4 +
      7 * (w1.eval (-(d / c))) ^ 6 = 0 := by
    linear_combination (80⁻¹ : K) * hevB
  obtain ⟨h3y, h27x⟩ := alignedSeventhSexticResolve_610 h7 hB
  have he1eval : ((3 : K[X]) * f2 - w1 ^ 2).eval (-(d / c)) = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat]
    linear_combination h3y
  have he2eval : ((27 : K[X]) * a3 - w1 ^ 3).eval (-(d / c)) = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat]
    linear_combination h27x
  obtain ⟨e1, he1⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    ((3 : K[X]) * f2 - w1 ^ 2) (-(d / c)) hdeg1 hroot he1eval
  obtain ⟨e2, he2⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    ((27 : K[X]) * a3 - w1 ^ 3) (-(d / c)) hdeg1 hroot he2eval
  refine ⟨e1, e2, he1, he2, ?_, ?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    linear_combination -htie6 -
      ((1440 : K[X]) * f2 * w1 - (2160 : K[X]) * a3 -
        (400 : K[X]) * w1 ^ 3 - (80 : K[X]) * e2 * h0) * he2 -
      ((2160 : K[X]) * f2 ^ 2 - (3600 : K[X]) * f2 * w1 ^ 2 +
        (960 : K[X]) * w1 ^ 4 + (720 : K[X]) * e1 * f2 * h0 -
        (960 : K[X]) * e1 * w1 ^ 2 * h0 + (480 : K[X]) * e2 * w1 * h0 +
        (240 : K[X]) * e1 ^ 2 * h0 ^ 2) * he1
  · apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    linear_combination hcore +
      ((17280 : K[X]) * a3 * w1 + (17280 : K[X]) * f2 ^ 2 -
        (23040 : K[X]) * f2 * w1 ^ 2 + (5120 : K[X]) * w1 ^ 4 +
        (640 : K[X]) * e2 * h0 * w1 - (103680 : K[X]) * a2 * h0 ^ 2 +
        Polynomial.C κ * ((1536 : K[X]) * h0 ^ 2 * w1 ^ 2 -
          (4608 : K[X]) * f2 * h0 ^ 2) +
        Polynomial.C μ * ((224 : K[X]) * h0 ^ 3 * w1) +
        Polynomial.C κ₃ * ((192 : K[X]) * h0 ^ 4)) * he2 +
      ((-(69120 : K[X])) * f2 ^ 2 * w1 + (63360 : K[X]) * f2 * w1 ^ 3 -
        (13440 : K[X]) * w1 ^ 5 - (23040 : K[X]) * e1 * f2 * h0 * w1 +
        (13440 : K[X]) * e1 * h0 * w1 ^ 3 +
        (5760 : K[X]) * e2 * f2 * h0 -
        (5760 : K[X]) * e2 * h0 * w1 ^ 2 -
        (7680 : K[X]) * e1 ^ 2 * h0 ^ 2 * w1 +
        (1920 : K[X]) * e1 * e2 * h0 ^ 2 +
        (311040 : K[X]) * a2 * h0 ^ 2 * w1 -
        (933120 : K[X]) * a1 * h0 ^ 4 +
        Polynomial.C κ * ((4608 : K[X]) * e1 * h0 ^ 3 * w1 +
          (13824 : K[X]) * f2 * h0 ^ 2 * w1 -
          (4608 : K[X]) * h0 ^ 2 * w1 ^ 3 -
          (1536 : K[X]) * e2 * h0 ^ 3) +
        Polynomial.C μ * ((336 : K[X]) * e1 * h0 ^ 4 +
          (1008 : K[X]) * f2 * h0 ^ 3 -
          (504 : K[X]) * h0 ^ 3 * w1 ^ 2) +
        Polynomial.C ν * ((120 : K[X]) * h0 ^ 5)) * he1

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the weight-thirty-five
integral forces its constant to vanish, and with it the whole seventh
defect. -/
theorem alignedNonsquareSeventh_defect_eq_zero_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : k[X]} {κ κ₆ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hI2 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ ^ 2 =
        Polynomial.C κ₆ * H ^ 35) :
    κ₆ = 0 ∧
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set I : k[X] :=
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 17) ^ 2 ∣ I ^ 2 := by
    refine ⟨Polynomial.C κ₆ * H, ?_⟩
    rw [hI2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₆ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 34 hH)
    have h34 := hI2
    rw [hG] at h34
    linear_combination h34
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₆ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk6 : κ₆ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hIzero : I = 0 := by
    have hsq : I ^ 2 = 0 := by
      rw [hI2, hk6]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk6, hIzero⟩

/-- Descent of the consumed degree-`8` row in the nonsquare chamber:
the `H¹⁴`-peeled core kills the septic block at BOTH simple roots, the
scalar resolution against the sixth-face sextic root tie pins
`3 f(a) = g₁(a)²` and `27 p₃(a) = g₁(a)³` at every root, the
simple-root transfer gives the NEW divisibilities `3 f - g₁² = H t₁`
and `27 p₃ - g₁³ = H t₂`, the sixth-face quotient itself becomes
divisible, `t = H (80 (t₂ - 3 t₁ g₁)² - 240 H t₁³)`, and cancelling
`H²` solves `q₃` OUTRIGHT. -/
theorem alignedNonsquareSeventh_solved_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 f t a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : k[X]} {κ κ₃ κ₅ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (ht : (58320 : k[X]) * a3 ^ 2 - (38880 : k[X]) * a3 * f * g1 -
        (6480 : k[X]) * f ^ 3 + (8640 : k[X]) * a3 * g1 ^ 3 +
        (12960 : k[X]) * f ^ 2 * g1 ^ 2 - (5040 : k[X]) * f * g1 ^ 4 +
        (560 : k[X]) * g1 ^ 6 = H * t) :
    ∃ t1 t2 : k[X],
      (3 : k[X]) * f - g1 ^ 2 = H * t1 ∧
      (27 : k[X]) * a3 - g1 ^ 3 = H * t2 ∧
      t = H * ((80 : k[X]) * (t2 - (3 : k[X]) * t1 * g1) ^ 2 -
        (240 : k[X]) * H * t1 ^ 3) ∧
      (2519424 : k[X]) * b3 =
        (466560 : k[X]) * a1 * g1 ^ 2 -
          (640 : k[X]) * g1 * (t2 - (3 : k[X]) * t1 * g1) ^ 2 +
          (103680 : k[X]) * a2 * t2 - (311040 : k[X]) * a2 * t1 * g1 +
          Polynomial.C κ * ((124416 : k[X]) * a2 * g1) -
          Polynomial.C κ₃ * ((192 : k[X]) * g1 ^ 3) +
          H * ((2799360 : k[X]) * a0 * g1 + (933120 : k[X]) * a1 * t1 +
            (7680 : k[X]) * g1 * t1 ^ 3 - (1920 : k[X]) * t1 ^ 2 * t2 +
            Polynomial.C κ * ((373248 : k[X]) * a1 -
              (4608 : k[X]) * g1 * t1 ^ 2 + (1536 : k[X]) * t1 * t2) -
            Polynomial.C κ₃ * ((192 : k[X]) * t2) -
            Polynomial.C κ₅ * ((16 : k[X]) * g1)) := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hcore :
      (-(466560 : k[X])) * a3 ^ 2 * g1 - (466560 : k[X]) * a3 * f ^ 2 +
          (622080 : k[X]) * a3 * f * g1 ^ 2 -
          (120960 : k[X]) * a3 * g1 ^ 4 + (207360 : k[X]) * f ^ 3 * g1 -
          (241920 : k[X]) * f ^ 2 * g1 ^ 3 +
          (80640 : k[X]) * f * g1 ^ 5 - (8320 : k[X]) * g1 ^ 7 +
          H * ((2799360 : k[X]) * a2 * a3 -
            (933120 : k[X]) * a2 * f * g1 +
            (207360 : k[X]) * a2 * g1 ^ 3 +
            Polynomial.C κ * ((124416 : k[X]) * a3 * f -
              (41472 : k[X]) * a3 * g1 ^ 2 -
              (41472 : k[X]) * f ^ 2 * g1 +
              (23040 : k[X]) * f * g1 ^ 3 - (3072 : k[X]) * g1 ^ 5)) +
          H ^ 2 * ((2799360 : k[X]) * a1 * f -
            (466560 : k[X]) * a1 * g1 ^ 2 - (2519424 : k[X]) * b3 +
            Polynomial.C κ * ((124416 : k[X]) * a2 * g1) -
            Polynomial.C κ₃ * ((5184 : k[X]) * a3)) +
          H ^ 3 * ((2799360 : k[X]) * a0 * g1 +
            Polynomial.C κ * ((373248 : k[X]) * a1) -
            Polynomial.C κ₅ * ((16 : k[X]) * g1)) = 0 := by
    have hI' := hI0
    simp only [alignedSeventhDefect610] at hI'
    rw [hD0, hE, hF0, hG, hg1, hf] at hI'
    apply mul_left_cancel₀ (pow_ne_zero 14 hH)
    linear_combination hI'
  have hkey : ∀ a : k, H.eval a = 0 →
      ((3 : k[X]) * f - g1 ^ 2).eval a = 0 ∧
      ((27 : k[X]) * a3 - g1 ^ 3).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun u : k[X] => u.eval a) hcore
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_neg, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hev
    rw [ha] at hev
    have hevB := congrArg (fun u : k[X] => u.eval a) ht
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hevB
    rw [ha] at hevB
    have h7 : 729 * (a3.eval a) ^ 2 * (g1.eval a) +
        729 * (a3.eval a) * (f.eval a) ^ 2 -
        972 * (a3.eval a) * (f.eval a) * (g1.eval a) ^ 2 +
        189 * (a3.eval a) * (g1.eval a) ^ 4 -
        324 * (f.eval a) ^ 3 * (g1.eval a) +
        378 * (f.eval a) ^ 2 * (g1.eval a) ^ 3 -
        126 * (f.eval a) * (g1.eval a) ^ 5 +
        13 * (g1.eval a) ^ 7 = 0 := by
      linear_combination (-(640⁻¹ : k)) * hev
    have hB : 729 * (a3.eval a) ^ 2 -
        486 * (a3.eval a) * (f.eval a) * (g1.eval a) -
        81 * (f.eval a) ^ 3 + 108 * (a3.eval a) * (g1.eval a) ^ 3 +
        162 * (f.eval a) ^ 2 * (g1.eval a) ^ 2 -
        63 * (f.eval a) * (g1.eval a) ^ 4 +
        7 * (g1.eval a) ^ 6 = 0 := by
      linear_combination (80⁻¹ : k) * hevB
    obtain ⟨h3y, h27x⟩ := alignedSeventhSexticResolve_610 h7 hB
    constructor
    · simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination h3y
    · simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination h27x
  obtain ⟨t1, ht1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hkey a ha).1)
  obtain ⟨t2, ht2⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hkey a ha).2)
  refine ⟨t1, t2, ht1, ht2, ?_, ?_⟩
  · apply mul_left_cancel₀ hH
    linear_combination -ht -
      ((1440 : k[X]) * f * g1 - (2160 : k[X]) * a3 -
        (400 : k[X]) * g1 ^ 3 - (80 : k[X]) * H * t2) * ht2 -
      ((2160 : k[X]) * f ^ 2 - (3600 : k[X]) * f * g1 ^ 2 +
        (960 : k[X]) * g1 ^ 4 + (720 : k[X]) * f * t1 * H -
        (960 : k[X]) * g1 ^ 2 * t1 * H + (480 : k[X]) * g1 * t2 * H +
        (240 : k[X]) * t1 ^ 2 * H ^ 2) * ht1
  · apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination -hcore +
      ((-(17280 : k[X])) * a3 * g1 - (17280 : k[X]) * f ^ 2 +
        (23040 : k[X]) * f * g1 ^ 2 - (5120 : k[X]) * g1 ^ 4 -
        (640 : k[X]) * H * g1 * t2 + (103680 : k[X]) * H * a2 +
        Polynomial.C κ * ((4608 : k[X]) * H * f -
          (1536 : k[X]) * H * g1 ^ 2) -
        Polynomial.C κ₃ * ((192 : k[X]) * H ^ 2)) * ht2 +
      ((69120 : k[X]) * f ^ 2 * g1 - (63360 : k[X]) * f * g1 ^ 3 +
        (13440 : k[X]) * g1 ^ 5 + (23040 : k[X]) * H * f * g1 * t1 -
        (5760 : k[X]) * H * f * t2 - (13440 : k[X]) * H * g1 ^ 3 * t1 +
        (5760 : k[X]) * H * g1 ^ 2 * t2 -
        (311040 : k[X]) * H * a2 * g1 +
        (7680 : k[X]) * H ^ 2 * g1 * t1 ^ 2 -
        (1920 : k[X]) * H ^ 2 * t1 * t2 +
        (933120 : k[X]) * H ^ 2 * a1 +
        Polynomial.C κ * ((4608 : k[X]) * H * g1 ^ 3 -
          (13824 : k[X]) * H * f * g1 -
          (4608 : k[X]) * H ^ 2 * g1 * t1 +
          (1536 : k[X]) * H ^ 2 * t2)) * ht1

/-! ## Source-facing seventh-row packets -/

/-- Source-facing squared weight-thirty-five integral of a normalized
aligned scale-two `(6,10)` source: the degree-`8` row is consumed into
`I² = κ₆ H³⁵` on top of the previous aligned packet. -/
theorem normalized610ScaleTwo_alignedSeventhFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ κ₅ κ₆ : K),
      q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₂ * H ^ 15 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ ^ 2 =
          Polynomial.C κ₄ * H ^ 25 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₆ * H ^ 35 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_610 hp hq hjac hH hp6' hq10' haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₃, hE⟩ :=
    alignedFourthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, aligned_q9_solved_610 haligned, hM, hD2,
    hE, hF2, hG, hI2⟩

/-- Exact square-chamber seventh packet of a normalized aligned
scale-two `(6,10)` source: the square root `I = ν₂ h₀³⁵`, the NEW
divisibilities `3 f₂ - w₁² = h₀ e₁` and `27 p₃ - w₁³ = h₀ e₂`
(resolving the sixth-face sextic tie at the root into exact pins), the
refined sixth-face quotient `s = 80 (e₂ - 3 e₁ w₁)² - 240 h₀ e₁³`, and
the twice-peeled seventh row with `q₃` tied at `h₀²`. -/
theorem normalized610ScaleTwo_alignedSeventhFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ ν κ₅ ν₂ : K) (w1 f2 s e1 e2 : K[X]),
      p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (58320 : K[X]) * p.coeff 3 ^ 2 -
            (38880 : K[X]) * p.coeff 3 * f2 * w1 -
            (6480 : K[X]) * f2 ^ 3 +
            (8640 : K[X]) * p.coeff 3 * w1 ^ 3 +
            (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
            (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 =
          h0 ^ 2 * s ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        s = (80 : K[X]) * (e2 - (3 : K[X]) * e1 * w1) ^ 2 -
          (240 : K[X]) * h0 * e1 ^ 3 ∧
        (-(640 : K[X])) * w1 * (e2 - (3 : K[X]) * e1 * w1) ^ 2 +
            h0 * ((7680 : K[X]) * e1 ^ 3 * w1 -
              (1920 : K[X]) * e1 ^ 2 * e2 -
              (311040 : K[X]) * e1 * p.coeff 2 * w1 +
              (103680 : K[X]) * e2 * p.coeff 2 -
              Polynomial.C μ * ((105 : K[X]) * w1 ^ 4)) +
            h0 ^ 2 * ((466560 : K[X]) * p.coeff 1 * w1 ^ 2 -
              (2519424 : K[X]) * q.coeff 3 +
              Polynomial.C κ * ((1536 : K[X]) * e1 * e2 -
                (4608 : K[X]) * e1 ^ 2 * w1 +
                (124416 : K[X]) * p.coeff 2 * w1) +
              Polynomial.C μ * ((168 : K[X]) * e1 * w1 ^ 2 -
                (224 : K[X]) * e2 * w1) -
              Polynomial.C κ₃ * ((192 : K[X]) * w1 ^ 3)) +
            h0 ^ 3 * ((933120 : K[X]) * e1 * p.coeff 1 -
              Polynomial.C μ * ((336 : K[X]) * e1 ^ 2 +
                (36288 : K[X]) * p.coeff 2) -
              Polynomial.C κ₃ * ((192 : K[X]) * e2) -
              Polynomial.C ν * ((90 : K[X]) * w1 ^ 2)) +
            h0 ^ 4 * ((2799360 : K[X]) * p.coeff 0 * w1 +
              Polynomial.C κ * ((373248 : K[X]) * p.coeff 1) -
              Polynomial.C ν * ((120 : K[X]) * e1) -
              Polynomial.C κ₅ * ((16 : K[X]) * w1)) =
          Polynomial.C ν₂ * h0 ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ =
          Polynomial.C μ * h0 ^ 15 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ =
          Polynomial.C ν * h0 ^ 25 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₂ * h0 ^ 35 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_610 hp hq hjac hH hp6' hq10' haligned
  obtain ⟨g, hg⟩ := alignedSquare_dvd_p5_610 hHsq hM
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hD⟩ := alignedSquareThird_sqrt_610 hh0 hHsq hD2
  have hEcore3 := alignedSquareThird_core_610 hh0 hHsq hg hD
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨w, hgw, hq7⟩ := alignedSquareThird_descent_610 hh0 hdeg1 hEcore3
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hp5 : p.coeff 5 = h0 ^ 3 * w := by rw [hg, hgw]; ring
  have hcore4 := alignedSquareFourth_core_610 hh0 hHsq hp5 hD hE4
  obtain ⟨r, htie4, hq6⟩ := alignedSquareFourth_tie_610 hcore4
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨ν, _hν2, hF⟩ := alignedSquareFifth_sqrt_610 hh0 hHsq hF2
  have hcore5 := alignedSquareFifth_core_610 hh0 hHsq hp5 hD hE4 hF
  obtain ⟨w1, f1, hw1, hf1, hq5⟩ :=
    alignedSquareFifth_descent_610 hh0 hdeg1 hcore5 htie4
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hp5w1 : p.coeff 5 = h0 ^ 4 * w1 := by rw [hp5, hw1]; ring
  have hcore6 := alignedSquareSixth_core_610 hh0 hHsq hp5w1 hf1 hD hE4
    hF hG
  obtain ⟨f2, hf2, hcore2⟩ :=
    alignedSquareSixth_descent_610 hh0 hdeg1 hcore6
  obtain ⟨s, htie6, _hq4⟩ := alignedSquareSixth_tie_610 hcore2
  have hp4f2 : p.coeff 4 = h0 ^ 2 * f2 := by rw [hf1, hf2]; ring
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨ν₂, _hν₂2, hI⟩ := alignedSquareSeventh_sqrt_610 hh0 hHsq hI2
  obtain ⟨e1, e2, he1, he2, hsref, hR⟩ :=
    alignedSquareSeventh_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hE4
      hF hG hI htie6
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, w1, f2, s, e1, e2, hp5w1, hp4f2, htie6,
    he1, he2, hsref, hR, hD, hE4, hF, hG, hI⟩

/-- Exact nonsquare-chamber seventh packet of a normalized aligned
scale-two `(6,10)` source: the forced `κ₆ = 0` and `I = 0`, the NEW
divisibilities `3 f - g₁² = H t₁` and `27 p₃ - g₁³ = H t₂` (the root
pins hold at BOTH simple roots), the refined sixth-face quotient
`t = H (80 (t₂ - 3 t₁ g₁)² - 240 H t₁³)`, and `q₃` solved OUTRIGHT. -/
theorem normalized610ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ : K) (g1 f t t1 t2 : K[X]),
      p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (58320 : K[X]) * p.coeff 3 ^ 2 -
            (38880 : K[X]) * p.coeff 3 * f * g1 -
            (6480 : K[X]) * f ^ 3 +
            (8640 : K[X]) * p.coeff 3 * g1 ^ 3 +
            (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
            (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 =
          H * t ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        t = H * ((80 : K[X]) * (t2 - (3 : K[X]) * t1 * g1) ^ 2 -
          (240 : K[X]) * H * t1 ^ 3) ∧
        (2519424 : K[X]) * q.coeff 3 =
          (466560 : K[X]) * p.coeff 1 * g1 ^ 2 -
            (640 : K[X]) * g1 * (t2 - (3 : K[X]) * t1 * g1) ^ 2 +
            (103680 : K[X]) * p.coeff 2 * t2 -
            (311040 : K[X]) * p.coeff 2 * t1 * g1 +
            Polynomial.C κ * ((124416 : K[X]) * p.coeff 2 * g1) -
            Polynomial.C κ₃ * ((192 : K[X]) * g1 ^ 3) +
            H * ((2799360 : K[X]) * p.coeff 0 * g1 +
              (933120 : K[X]) * p.coeff 1 * t1 +
              (7680 : K[X]) * g1 * t1 ^ 3 -
              (1920 : K[X]) * t1 ^ 2 * t2 +
              Polynomial.C κ * ((373248 : K[X]) * p.coeff 1 -
                (4608 : K[X]) * g1 * t1 ^ 2 +
                (1536 : K[X]) * t1 * t2) -
              Polynomial.C κ₃ * ((192 : K[X]) * t2) -
              Polynomial.C κ₅ * ((16 : K[X]) * g1)) ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 ∧
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_610 hp hq hjac hH hp6' hq10' haligned
  obtain ⟨g, hg⟩ := alignedNonsquare_dvd_p5_610 hHdegree hnsq hM
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk2, hD0⟩ :=
    alignedNonsquareThird_defect_eq_zero_610 hH hHdegree hnsq hD2
  obtain ⟨g1, hg1, hq7⟩ :=
    alignedNonsquareThird_solved_610 hH hHdegree hnsq hg hD0
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hp5 : p.coeff 5 = H ^ 2 * g1 := by rw [hg, hg1]; ring
  have hcore4 := alignedNonsquareFourth_core_610 hH hp5 hD0 hE4
  obtain ⟨f, hf⟩ := alignedNonsquareFourth_dvd_p4_610 hHdegree hnsq hcore4
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk4, hF0⟩ :=
    alignedNonsquareFifth_defect_eq_zero_610 hH hHdegree hnsq hF2
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hcore6 := alignedNonsquareSixth_core_610 hH hp5 hf hD0 hE4 hF0 hG
  obtain ⟨t, ht⟩ := alignedNonsquareSixth_dvd_610 hHdegree hnsq hcore6
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk6, hI0⟩ :=
    alignedNonsquareSeventh_defect_eq_zero_610 hH hHdegree hnsq hI2
  obtain ⟨t1, t2, ht1, ht2, htref, hq3⟩ :=
    alignedNonsquareSeventh_solved_610 hH hHdegree hnsq hp5 hf hD0 hE4
      hF0 hG hI0 ht
  exact ⟨κ, κ₃, κ₅, g1, f, t, t1, t2, hp5, hf, ht, ht1, ht2, htref,
    hq3, hD0, hE4, hF0, hG, hI0⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`8`
aligned row (solved forms of `q₃`, the refined quotients, and the
factored defect relations are in the two chamber packets above).
Neither chamber is excluded and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedSeventhFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (w1 f2 e1 e2 : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t1 t2 : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedSeventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, w1, f2, s, e1, e2, hp5, hp4, _htie6,
      he1, he2, _hsref, _hR, _hD, _hE, _hF, _hG, _hI⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, w1, f2, e1, e2, hp5, hp4, he1, he2⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, g1, f, t, t1, t2, hp5, hf, _ht, ht1, ht2,
      _htref, _hq3, _hD0, _hE, _hF0, _hG, _hI0⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t1, t2, hp5, hf, ht1, ht2⟩

/-- Root data of the consumed degree-`8` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇, p₄, q₆` vanishes, and
in BOTH chambers the sixth-face sextic tie is RESOLVED at the root
into the exact pins `3·(p₄-quotient)(a) = (p₅-quotient)(a)²` and
`27 p₃(a) = (p₅-quotient)(a)³`; in the square chamber the twice-peeled
seventh row leaves the honest residual branch
`w₁(a) = 0 ∨ e₂(a) = 3 e₁(a) w₁(a)`. -/
theorem normalized610ScaleTwo_alignedSeventhFace_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (q.coeff 7).eval a = 0 ∧ (p.coeff 4).eval a = 0 ∧
      (q.coeff 6).eval a = 0 ∧
      ((∃ h0 w1 f2 e1 e2 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          3 * f2.eval a = w1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = w1.eval a ^ 3 ∧
          (w1.eval a = 0 ∨
            e2.eval a = 3 * e1.eval a * w1.eval a)) ∨
        (∃ g1 f t1 t2 : K[X], p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          3 * f.eval a = g1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = g1.eval a ^ 3)) := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hH
      simp [hHsq, hzero]
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, μA, κ₃A, νA, w, r, w1', f1', hp5w, hq9, hq8, hq7,
      htie4, hq6, hw1', hf1', _hq5', _hF5⟩ := hpacket5
    have hpacket7 :=
      normalized610ScaleTwo_alignedSeventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket7
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, ν₂B, w1, f2, s, e1, e2, hp5w1, hp4f2,
      _htie6, he1, he2, _hsref, hR, _hD, _hE, _hF, _hG, _hI⟩ := hpacket7
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hr : r = h0 ^ 2 *
        ((270 : K[X]) * f2 ^ 2 - (90 : K[X]) * f2 * w1' ^ 2 +
          (10 : K[X]) * w1' ^ 4) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
      rw [hp4f2, hw1'] at htie4
      linear_combination -htie4
    have hra : r.eval a = 0 := by
      rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hpin1 : 3 * f2.eval a = w1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = w1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, e1, e2, hh0, hHsq, hroot, hp5w1, hp4f2,
        he1, he2, hpin1, hpin2, ?_⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5w1, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (7 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hp4f2, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      have h486 : (486 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 6).eval a = 0 := by
        linear_combination hev + hra
      exact (mul_eq_zero.mp h486).resolve_left
        (by norm_num : (486 : K) ≠ 0)
    · have hevR := congrArg (fun t : K[X] => t.eval a) hR
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_neg, Polynomial.eval_ofNat] at hevR
      rw [hroot] at hevR
      have h640 : (-(640 : K)) *
          (w1.eval a *
            (e2.eval a - 3 * e1.eval a * w1.eval a) ^ 2) = 0 := by
        linear_combination hevR
      have hprod : w1.eval a *
          (e2.eval a - 3 * e1.eval a * w1.eval a) ^ 2 = 0 :=
        (mul_eq_zero.mp h640).resolve_left
          (by norm_num : (-(640 : K)) ≠ 0)
      rcases mul_eq_zero.mp hprod with hw | hsq2
      · exact Or.inl hw
      · refine Or.inr ?_
        have hz := (pow_eq_zero_iff
          (by norm_num : (2 : ℕ) ≠ 0)).mp hsq2
        linear_combination hz
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, κ₃A, g1', f', _hp5', hq9, hq8, hq7, _hf', hq6, _hq5',
      _hD0', _hE', _hF0'⟩ := hpacket5
    have hpacket7 :=
      normalized610ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket7
    obtain ⟨κB, κ₃B, κ₅B, g1, f, t, t1, t2, hp5, hf, _ht, ht1, ht2,
      _htref, _hq3, _hD0, _hE, _hF0, _hG, _hI0⟩ := hpacket7
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hpin1 : 3 * f.eval a = g1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = g1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, t1, t2, hp5, hf, ht1, ht2, hpin1, hpin2⟩⟩
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hf, Polynomial.eval_mul, hroot, zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (486 : K) ≠ 0)

#print axioms alignedSeventhCoefficientJacobianRow_610
#print axioms alignedSeventhDefect_weightedDerivative_identity_610
#print axioms alignedSeventhDefectRow_eq_zero_610
#print axioms alignedSeventhDefectPowerRelation_610
#print axioms alignedSquareSeventh_sqrt_610
#print axioms alignedSeventhSexticResolve_610
#print axioms alignedSquareSeventh_descent_610
#print axioms alignedNonsquareSeventh_defect_eq_zero_610
#print axioms alignedNonsquareSeventh_solved_610
#print axioms normalized610ScaleTwo_alignedSeventhFace_packet
#print axioms normalized610ScaleTwo_alignedSeventhFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedSeventhFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedSeventhFace_rootData

end Max11DegreeRoutes
