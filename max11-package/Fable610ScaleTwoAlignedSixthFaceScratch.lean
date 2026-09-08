import Fable610ScaleTwoAlignedFifthFaceScratch

/-! # Sixth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedFifthFaceScratch` consumed the degree-`10`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
squared weight-twenty-five integral `F² = κ₄ H²⁵`, with the square
chamber upgraded to `p₅ = h₀⁴ w₁`, `p₄ = h₀ f₁` and the residual root
branch `w₁(a) = 0 ∨ f₁(a) = 0`, and the nonsquare chamber solved
outright (`F = 0`).  This file consumes the next unused aligned row,
the degree-`9` Jacobian coefficient — the first row that sees `p₀` and
`q₄`.

At the source level, modulo the face `N = 0`, the consumed
`C = 9 q₈ H - 15 p₄ H³ - 5 p₅² - κ H⁵ = 0`, and the consumed
degree-`12`, `11`, `10` rows, the degree-`9` row is the weighted
derivative of the cleared sixth defect

`G = 174960 p₀ H¹⁵ - 104976 q₄ H¹³ + 116640 p₁ p₅ H¹²
  + 116640 p₂ p₄ H¹² + 58320 p₃² H¹² - 19440 p₂ p₅² H⁹
  - 38880 p₃ p₄ p₅ H⁹ - 6480 p₄³ H⁹ + 8640 p₃ p₅³ H⁶
  + 12960 p₄² p₅² H⁶ - 5040 p₄ p₅⁴ H³ + 560 p₅⁶
  + κ (15552 p₂ H¹⁴ + 5184 p₃ p₅ H¹¹ + 2592 p₄² H¹¹
       - 1728 p₄ p₅² H⁸ + 240 p₅⁴ H⁵)
  - (1512 p₃ H⁶ + 252 p₄ p₅ H³ - 35 p₅³) D - 216 p₄ H³ E - 15 p₅ F`,

kept in factored form through the third, fourth, and fifth defects,
via the exact multiplier identity

`17496 H¹¹ · row₉[p₆ = H³, q₁₀ = H⁵] = (H G' - 15 G H')
  - 52488 H¹¹ p₁' N + 5832 H¹¹ p₁ N'
  + (15552 H¹⁰ p₂' + 3888 H⁹ p₂ H') C - 3888 H¹⁰ p₂ C'
  + (1080 p₃ H⁶ + 1260 p₄ p₅ H³ + 35 p₅³)(2 H D' - 15 D H')
  + (360 p₄ H³ + 180 p₅²)(H E' - 10 E H')
  + 15 p₅ (2 H F' - 25 F H')`.

On the aligned face every correction vanishes, so `H G' = 15 G H'` and
the weight-fifteen first integral `G = κ₅ H¹⁵` holds CHAMBER-FREE (the
even exponent needs no square root of `H`, exactly as for `E`).

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀ f₁`, `D = μ h₀¹⁵`,
  `E = κ₃ H¹⁰`, `F = ν h₀²⁵`): cancelling `h₀²¹` leaves a core whose
  `h₀`-free part is `-6480 f₁³`, so at the root `f₁(a) = 0`
  unconditionally — the fifth-face residual branch
  `w₁(a) = 0 ∨ f₁(a) = 0` is RESOLVED, and the linear-root transfer
  gives the second-order kill `p₄ = h₀² f₂`.  Cancelling `h₀³` more
  yields the sextic tie
  `58320 p₃² - 38880 p₃ f₂ w₁ - 6480 f₂³ + 8640 p₃ w₁³
  + 12960 f₂² w₁² - 5040 f₂ w₁⁴ + 560 w₁⁶ = h₀² s`
  — the FIRST constraint on `p₃` in the aligned tower (as a quadratic
  in `27 p₃` its discriminant is `2²·3⁷ (3 f₂ - w₁²)³`, not a square in
  general, so no clean divisibility is extracted) — and `q₄` is solved
  OUTRIGHT (no `h₀` power left on `q₄`).  Backwired into the fifth row,
  `p₄ = h₀² f₂` divides the peeled `q₅` relation by `h₀²`, solving `q₅`
  outright as well, and turns the fourth-row quotient into
  `r = h₀² (270 f₂² - 90 f₂ w₁² + 10 w₁⁴)`, so `r(a) = 0` and the NEW
  root gain `q₆(a) = 0`.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`): cancelling `H¹²` leaves
  a core whose `H`-free part is the SAME sextic block in
  `(p₃, f, g₁)`; it vanishes at both simple roots (the sextic root tie
  now holds at every root of `H`), the quotient `t` with
  `block = H t` exists, and `q₄` is solved against `t` — with the
  honest inhomogeneous root relation for `q₄(a)`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `g₁ = 0`, `f = 0`, `s = 0`, `t = 0`, `κ = 0`,
`μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₅ = 0`) are not excluded, and the
constants `κ`, `κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅` are preserved where
not forced.  The next unused Keller row on the aligned face is the
degree-`8` Jacobian coefficient, the first row that sees `q₃` (pairs
`(0,9), (1,8), (2,7), (3,6), (4,5), (5,4), (6,3)`; expected
weight-`35/2` defect, odd exponent, so a squared weight-thirty-five
integral with a square/nonsquare split like `D` and `F`).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`9` Keller coefficient on the aligned face -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`9` Jacobian coefficient, the first
aligned row that sees `p₀` and `q₄`. -/
theorem alignedSixthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 4).derivative +
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
        (7, 2), (8, 1),
        (9, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
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
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned sixth defect -/

/-- Cleared sixth defect of the degree-`9` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
and the fifth defect `F`.  On the aligned face it is a polynomial
first integral of weight fifteen with an EVEN exponent. -/
def alignedSixthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (174960 : K[X]) * a0 * H ^ 15 - (104976 : K[X]) * b4 * H ^ 13 +
    (116640 : K[X]) * a1 * a5 * H ^ 12 +
    (116640 : K[X]) * a2 * a4 * H ^ 12 +
    (58320 : K[X]) * a3 ^ 2 * H ^ 12 -
    (19440 : K[X]) * a2 * a5 ^ 2 * H ^ 9 -
    (38880 : K[X]) * a3 * a4 * a5 * H ^ 9 -
    (6480 : K[X]) * a4 ^ 3 * H ^ 9 +
    (8640 : K[X]) * a3 * a5 ^ 3 * H ^ 6 +
    (12960 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 -
    (5040 : K[X]) * a4 * a5 ^ 4 * H ^ 3 + (560 : K[X]) * a5 ^ 6 +
    Polynomial.C κ *
      ((15552 : K[X]) * a2 * H ^ 14 + (5184 : K[X]) * a3 * a5 * H ^ 11 +
        (2592 : K[X]) * a4 ^ 2 * H ^ 11 -
        (1728 : K[X]) * a4 * a5 ^ 2 * H ^ 8 +
        (240 : K[X]) * a5 ^ 4 * H ^ 5) -
    ((1512 : K[X]) * a3 * H ^ 6 + (252 : K[X]) * a4 * a5 * H ^ 3 -
        (35 : K[X]) * a5 ^ 3) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (216 : K[X]) * a4 * H ^ 3 *
      alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ -
    (15 : K[X]) * a5 *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`9` Jacobian expression with the
weighted derivative of `G`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13`,
degree-`12`, degree-`11`, and degree-`10` rows. -/
theorem alignedSixthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (17496 : K[X]) * H ^ 11 *
        ((H ^ 3).derivative * (b4 * (4 : K[X])) +
          a5.derivative * (b5 * (5 : K[X])) +
          a4.derivative * (b6 * (6 : K[X])) +
          a3.derivative * (b7 * (7 : K[X])) +
          a2.derivative * (b8 * (8 : K[X])) +
          a1.derivative * (b9 * (9 : K[X])) +
          a0.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b4.derivative +
          (a5 * (5 : K[X])) * b5.derivative +
          (a4 * (4 : K[X])) * b6.derivative +
          (a3 * (3 : K[X])) * b7.derivative +
          (a2 * (2 : K[X])) * b8.derivative +
          a1 * b9.derivative)) =
      (H *
          (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7
            κ).derivative -
        (15 : K[X]) *
          alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ *
          H.derivative) -
        (52488 : K[X]) * H ^ 11 * a1.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) +
        (5832 : K[X]) * H ^ 11 * a1 *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9).derivative +
        ((15552 : K[X]) * H ^ 10 * a2.derivative +
            (3888 : K[X]) * H ^ 9 * a2 * H.derivative) *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) -
        (3888 : K[X]) * H ^ 10 * a2 *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5).derivative +
        ((1080 : K[X]) * a3 * H ^ 6 + (1260 : K[X]) * a4 * a5 * H ^ 3 +
            (35 : K[X]) * a5 ^ 3) *
          ((2 : K[X]) * H *
              (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
            (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
              H.derivative) +
        ((360 : K[X]) * a4 * H ^ 3 + (180 : K[X]) * a5 ^ 2) *
          (H * (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative -
            (10 : K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ *
              H.derivative) +
        (15 : K[X]) * a5 *
          ((2 : K[X]) * H *
              (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7
                κ).derivative -
            (25 : K[X]) *
              alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ *
              H.derivative) := by
  simp only [alignedSixthDefect610, alignedFifthDefect610,
    alignedFourthDefect610, alignedThirdDefect610,
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

/-- On the aligned face, with the consumed degree-`13`, degree-`12`,
degree-`11`, and degree-`10` rows, the degree-`9` row is the weighted
derivative `H G' - 15 G H' = 0`. -/
theorem alignedSixthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    H *
        (alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (15 : K[X]) *
        alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedSixthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC3, hC2] at hrow
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
  have hid := alignedSixthDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
    (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hDrow, hErow, hFrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-fifteen polynomial first integral of the aligned `(6,10)`
sixth defect: `G = κ₅ H¹⁵`.  The even exponent makes the integral
chamber-free — no square root of `H` is required. -/
theorem alignedSixthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₅ : K,
      alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₅ * H ^ 15 := by
  let G : K[X] :=
    alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow : H * G.derivative - (15 : K[X]) * G * H.derivative = 0 := by
    simpa only [G] using
      alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC15 : Polynomial.C (15 : K) = (15 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian G (H ^ 15) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      G * (Polynomial.C (15 : K) * H ^ (15 - 1) * H.derivative) -
          G.derivative * H ^ 15 =
          H ^ 14 *
            (Polynomial.C (15 : K) * G * H.derivative -
              H * G.derivative) := by
        ring
      _ = 0 := by
        rw [hC15]
        have hfac :
            (15 : K[X]) * G * H.derivative - H * G.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 15 hH) hW

/-! ## Square chamber -/

/-- Cleared square-core form of the sixth defect relation: cancelling
`h₀²¹` from `G = κ₅ h₀³⁰` on `p₅ = h₀⁴ w₁`, `p₄ = h₀ f₁`, `D = μ h₀¹⁵`,
`E = κ₃ H¹⁰`, `F = ν h₀²⁵` leaves the chamber core with the `h₀`-free
cube `-6480 f₁³`. -/
theorem alignedSquareSixth_core_610 {K : Type*} [Field K] [CharZero K]
    {H h0 w1 f1 a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 : K[X]} {κ μ κ₃ ν κ₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp5 : a5 = h0 ^ 4 * w1)
    (hp4 : a4 = h0 * f1)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15) :
    (174960 : K[X]) * a0 * h0 ^ 9 - (104976 : K[X]) * b4 * h0 ^ 5 +
        (116640 : K[X]) * a1 * w1 * h0 ^ 7 +
        (116640 : K[X]) * a2 * f1 * h0 ^ 4 +
        (58320 : K[X]) * a3 ^ 2 * h0 ^ 3 -
        (19440 : K[X]) * a2 * w1 ^ 2 * h0 ^ 5 -
        (38880 : K[X]) * a3 * f1 * w1 * h0 ^ 2 -
        (6480 : K[X]) * f1 ^ 3 +
        (8640 : K[X]) * a3 * w1 ^ 3 * h0 ^ 3 +
        (12960 : K[X]) * f1 ^ 2 * w1 ^ 2 * h0 -
        (5040 : K[X]) * f1 * w1 ^ 4 * h0 ^ 2 +
        (560 : K[X]) * w1 ^ 6 * h0 ^ 3 +
        Polynomial.C κ *
          ((15552 : K[X]) * a2 * h0 ^ 7 +
            (5184 : K[X]) * a3 * w1 * h0 ^ 5 +
            (2592 : K[X]) * f1 ^ 2 * h0 ^ 3 -
            (1728 : K[X]) * f1 * w1 ^ 2 * h0 ^ 4 +
            (240 : K[X]) * w1 ^ 4 * h0 ^ 5) -
        Polynomial.C μ *
          ((1512 : K[X]) * a3 * h0 ^ 6 +
            (252 : K[X]) * f1 * w1 * h0 ^ 5 -
            (35 : K[X]) * w1 ^ 3 * h0 ^ 6) -
        Polynomial.C κ₃ * ((216 : K[X]) * f1 * h0 ^ 6) -
        Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 8) =
      Polynomial.C κ₅ * h0 ^ 9 := by
  have hG' := hG
  simp only [alignedSixthDefect610] at hG'
  rw [hD, hE, hF, hHsq, hp5, hp4] at hG'
  apply mul_left_cancel₀ (pow_ne_zero 21 hh0)
  linear_combination hG'

/-- Descent of the consumed degree-`9` row in the square chamber: at
the root of `h₀` the core kills `f₁` unconditionally — resolving the
fifth-face residual branch `w₁(a) = 0 ∨ f₁(a) = 0` — so `f₁ = h₀ f₂`
and the core peels once more. -/
theorem alignedSquareSixth_descent_610 {K : Type*} [Field K] [CharZero K]
    {h0 w1 f1 a0 a1 a2 a3 b4 : K[X]} {κ μ κ₃ ν κ₅ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hcore :
      (174960 : K[X]) * a0 * h0 ^ 9 - (104976 : K[X]) * b4 * h0 ^ 5 +
          (116640 : K[X]) * a1 * w1 * h0 ^ 7 +
          (116640 : K[X]) * a2 * f1 * h0 ^ 4 +
          (58320 : K[X]) * a3 ^ 2 * h0 ^ 3 -
          (19440 : K[X]) * a2 * w1 ^ 2 * h0 ^ 5 -
          (38880 : K[X]) * a3 * f1 * w1 * h0 ^ 2 -
          (6480 : K[X]) * f1 ^ 3 +
          (8640 : K[X]) * a3 * w1 ^ 3 * h0 ^ 3 +
          (12960 : K[X]) * f1 ^ 2 * w1 ^ 2 * h0 -
          (5040 : K[X]) * f1 * w1 ^ 4 * h0 ^ 2 +
          (560 : K[X]) * w1 ^ 6 * h0 ^ 3 +
          Polynomial.C κ *
            ((15552 : K[X]) * a2 * h0 ^ 7 +
              (5184 : K[X]) * a3 * w1 * h0 ^ 5 +
              (2592 : K[X]) * f1 ^ 2 * h0 ^ 3 -
              (1728 : K[X]) * f1 * w1 ^ 2 * h0 ^ 4 +
              (240 : K[X]) * w1 ^ 4 * h0 ^ 5) -
          Polynomial.C μ *
            ((1512 : K[X]) * a3 * h0 ^ 6 +
              (252 : K[X]) * f1 * w1 * h0 ^ 5 -
              (35 : K[X]) * w1 ^ 3 * h0 ^ 6) -
          Polynomial.C κ₃ * ((216 : K[X]) * f1 * h0 ^ 6) -
          Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 8) =
        Polynomial.C κ₅ * h0 ^ 9) :
    ∃ f2 : K[X], f1 = h0 * f2 ∧
      (174960 : K[X]) * a0 * h0 ^ 6 - (104976 : K[X]) * b4 * h0 ^ 2 +
          (116640 : K[X]) * a1 * w1 * h0 ^ 4 +
          (116640 : K[X]) * a2 * f2 * h0 ^ 2 +
          (58320 : K[X]) * a3 ^ 2 -
          (19440 : K[X]) * a2 * w1 ^ 2 * h0 ^ 2 -
          (38880 : K[X]) * a3 * f2 * w1 - (6480 : K[X]) * f2 ^ 3 +
          (8640 : K[X]) * a3 * w1 ^ 3 +
          (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
          (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 +
          Polynomial.C κ *
            ((15552 : K[X]) * a2 * h0 ^ 4 +
              (5184 : K[X]) * a3 * w1 * h0 ^ 2 +
              (2592 : K[X]) * f2 ^ 2 * h0 ^ 2 -
              (1728 : K[X]) * f2 * w1 ^ 2 * h0 ^ 2 +
              (240 : K[X]) * w1 ^ 4 * h0 ^ 2) -
          Polynomial.C μ *
            ((1512 : K[X]) * a3 * h0 ^ 3 +
              (252 : K[X]) * f2 * w1 * h0 ^ 3 -
              (35 : K[X]) * w1 ^ 3 * h0 ^ 3) -
          Polynomial.C κ₃ * ((216 : K[X]) * f2 * h0 ^ 4) -
          Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 5) =
        Polynomial.C κ₅ * h0 ^ 6 := by
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
  have h3 : (6480 : K) * f1.eval (-(d / c)) ^ 3 = 0 := by
    linear_combination -hev
  have h3' : f1.eval (-(d / c)) ^ 3 = 0 :=
    (mul_eq_zero.mp h3).resolve_left (by norm_num : (6480 : K) ≠ 0)
  have hf1a : f1.eval (-(d / c)) = 0 :=
    (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h3'
  obtain ⟨f2, hf2⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 f1 (-(d / c)) hdeg1
      hroot hf1a
  refine ⟨f2, hf2, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
  rw [hf2] at hcore
  linear_combination hcore

/-- The consumed degree-`9` row in the square chamber: the sextic tie
`58320 p₃² - 38880 p₃ f₂ w₁ - 6480 f₂³ + 8640 p₃ w₁³ + 12960 f₂² w₁²
- 5040 f₂ w₁⁴ + 560 w₁⁶ = h₀² s` — the first constraint on `p₃` in the
aligned tower — and the quartic coefficient `q₄` solved OUTRIGHT
against the new quotient `s`. -/
theorem alignedSquareSixth_tie_610 {K : Type*} [Field K] [CharZero K]
    {h0 w1 f2 a0 a1 a2 a3 b4 : K[X]} {κ μ κ₃ ν κ₅ : K}
    (hcore :
      (174960 : K[X]) * a0 * h0 ^ 6 - (104976 : K[X]) * b4 * h0 ^ 2 +
          (116640 : K[X]) * a1 * w1 * h0 ^ 4 +
          (116640 : K[X]) * a2 * f2 * h0 ^ 2 +
          (58320 : K[X]) * a3 ^ 2 -
          (19440 : K[X]) * a2 * w1 ^ 2 * h0 ^ 2 -
          (38880 : K[X]) * a3 * f2 * w1 - (6480 : K[X]) * f2 ^ 3 +
          (8640 : K[X]) * a3 * w1 ^ 3 +
          (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
          (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 +
          Polynomial.C κ *
            ((15552 : K[X]) * a2 * h0 ^ 4 +
              (5184 : K[X]) * a3 * w1 * h0 ^ 2 +
              (2592 : K[X]) * f2 ^ 2 * h0 ^ 2 -
              (1728 : K[X]) * f2 * w1 ^ 2 * h0 ^ 2 +
              (240 : K[X]) * w1 ^ 4 * h0 ^ 2) -
          Polynomial.C μ *
            ((1512 : K[X]) * a3 * h0 ^ 3 +
              (252 : K[X]) * f2 * w1 * h0 ^ 3 -
              (35 : K[X]) * w1 ^ 3 * h0 ^ 3) -
          Polynomial.C κ₃ * ((216 : K[X]) * f2 * h0 ^ 4) -
          Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 5) =
        Polynomial.C κ₅ * h0 ^ 6) :
    ∃ s : K[X],
      (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f2 * w1 -
          (6480 : K[X]) * f2 ^ 3 + (8640 : K[X]) * a3 * w1 ^ 3 +
          (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
          (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 =
        h0 ^ 2 * s ∧
      (104976 : K[X]) * b4 =
        (174960 : K[X]) * a0 * h0 ^ 4 +
          (116640 : K[X]) * a1 * w1 * h0 ^ 2 +
          (116640 : K[X]) * a2 * f2 - (19440 : K[X]) * a2 * w1 ^ 2 + s +
          Polynomial.C κ *
            ((15552 : K[X]) * a2 * h0 ^ 2 + (5184 : K[X]) * a3 * w1 +
              (2592 : K[X]) * f2 ^ 2 - (1728 : K[X]) * f2 * w1 ^ 2 +
              (240 : K[X]) * w1 ^ 4) -
          Polynomial.C μ *
            ((1512 : K[X]) * a3 * h0 + (252 : K[X]) * f2 * w1 * h0 -
              (35 : K[X]) * w1 ^ 3 * h0) -
          Polynomial.C κ₃ * ((216 : K[X]) * f2 * h0 ^ 2) -
          Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 3) -
          Polynomial.C κ₅ * h0 ^ 4 := by
  refine ⟨(104976 : K[X]) * b4 - (174960 : K[X]) * a0 * h0 ^ 4 -
      (116640 : K[X]) * a1 * w1 * h0 ^ 2 - (116640 : K[X]) * a2 * f2 +
      (19440 : K[X]) * a2 * w1 ^ 2 -
      Polynomial.C κ *
        ((15552 : K[X]) * a2 * h0 ^ 2 + (5184 : K[X]) * a3 * w1 +
          (2592 : K[X]) * f2 ^ 2 - (1728 : K[X]) * f2 * w1 ^ 2 +
          (240 : K[X]) * w1 ^ 4) +
      Polynomial.C μ *
        ((1512 : K[X]) * a3 * h0 + (252 : K[X]) * f2 * w1 * h0 -
          (35 : K[X]) * w1 ^ 3 * h0) +
      Polynomial.C κ₃ * ((216 : K[X]) * f2 * h0 ^ 2) +
      Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 3) +
      Polynomial.C κ₅ * h0 ^ 4, ?_, ?_⟩
  · linear_combination hcore
  · ring

/-- Backwired fifth row in the square chamber: the new second-order
kill `f₁ = h₀ f₂` divides the peeled quintic relation by `h₀²`, solving
`q₅` outright. -/
theorem alignedSquareSixth_q5Upgrade_610 {K : Type*} [Field K] [CharZero K]
    {h0 w1 f1 f2 a1 a2 a3 b5 : K[X]} {κ μ κ₃ ν : K}
    (hh0 : h0 ≠ 0) (hf2 : f1 = h0 * f2)
    (hq5 : (5832 : K[X]) * b5 * h0 ^ 2 =
      (9720 : K[X]) * a1 * h0 ^ 6 + (6480 : K[X]) * a2 * w1 * h0 ^ 4 +
        (6480 : K[X]) * a3 * f1 * h0 -
        (1080 : K[X]) * a3 * w1 ^ 2 * h0 ^ 2 -
        (1080 : K[X]) * f1 ^ 2 * w1 + (480 : K[X]) * f1 * w1 ^ 3 * h0 -
        (56 : K[X]) * w1 ^ 5 * h0 ^ 2 +
        Polynomial.C κ *
          ((864 : K[X]) * a3 * h0 ^ 4 +
            (288 : K[X]) * f1 * w1 * h0 ^ 3 -
            (32 : K[X]) * w1 ^ 3 * h0 ^ 4) -
        Polynomial.C μ *
          ((84 : K[X]) * f1 * h0 ^ 4 + (7 : K[X]) * w1 ^ 2 * h0 ^ 5) -
        Polynomial.C κ₃ * ((12 : K[X]) * w1 * h0 ^ 6) -
        Polynomial.C ν * h0 ^ 7) :
    (5832 : K[X]) * b5 =
      (9720 : K[X]) * a1 * h0 ^ 4 + (6480 : K[X]) * a2 * w1 * h0 ^ 2 +
        (6480 : K[X]) * a3 * f2 - (1080 : K[X]) * a3 * w1 ^ 2 -
        (1080 : K[X]) * f2 ^ 2 * w1 + (480 : K[X]) * f2 * w1 ^ 3 -
        (56 : K[X]) * w1 ^ 5 +
        Polynomial.C κ *
          ((864 : K[X]) * a3 * h0 ^ 2 +
            (288 : K[X]) * f2 * w1 * h0 ^ 2 -
            (32 : K[X]) * w1 ^ 3 * h0 ^ 2) -
        Polynomial.C μ *
          ((84 : K[X]) * f2 * h0 ^ 3 + (7 : K[X]) * w1 ^ 2 * h0 ^ 3) -
        Polynomial.C κ₃ * ((12 : K[X]) * w1 * h0 ^ 4) -
        Polynomial.C ν * h0 ^ 5 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
  rw [hf2] at hq5
  linear_combination hq5

/-! ## Nonsquare chamber -/

/-- Cleared nonsquare-core form of the sixth defect relation:
cancelling `H¹²` from `G = κ₅ H¹⁵` on `p₅ = H² g₁`, `p₄ = H f`,
`D = 0`, `F = 0` leaves the chamber core whose `H`-free part is the
same sextic block as in the square chamber. -/
theorem alignedNonsquareSixth_core_610 {K : Type*} [Field K] [CharZero K]
    {H g1 f a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0) (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15) :
    (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f * g1 -
        (6480 : K[X]) * f ^ 3 + (8640 : K[X]) * a3 * g1 ^ 3 +
        (12960 : K[X]) * f ^ 2 * g1 ^ 2 - (5040 : K[X]) * f * g1 ^ 4 +
        (560 : K[X]) * g1 ^ 6 -
        (104976 : K[X]) * b4 * H + (116640 : K[X]) * a2 * f * H -
        (19440 : K[X]) * a2 * g1 ^ 2 * H +
        Polynomial.C κ *
          ((5184 : K[X]) * a3 * g1 * H + (2592 : K[X]) * f ^ 2 * H -
            (1728 : K[X]) * f * g1 ^ 2 * H +
            (240 : K[X]) * g1 ^ 4 * H +
            (15552 : K[X]) * a2 * H ^ 2) +
        (116640 : K[X]) * a1 * g1 * H ^ 2 -
        Polynomial.C κ₃ * ((216 : K[X]) * f * H ^ 2) +
        (174960 : K[X]) * a0 * H ^ 3 =
      Polynomial.C κ₅ * H ^ 3 := by
  have hG' := hG
  simp only [alignedSixthDefect610] at hG'
  rw [hD0, hE, hF0, hg1, hf] at hG'
  apply mul_left_cancel₀ (pow_ne_zero 12 hH)
  linear_combination hG'

/-- At every root of `H` the nonsquare core evaluates to the sextic
root tie — the same normalized form as the square-chamber tie. -/
theorem alignedNonsquareSixth_rootTie_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f a0 a1 a2 a3 b4 : K[X]} {κ κ₃ κ₅ : K}
    (hcore :
      (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f * g1 -
          (6480 : K[X]) * f ^ 3 + (8640 : K[X]) * a3 * g1 ^ 3 +
          (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
          (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 -
          (104976 : K[X]) * b4 * H + (116640 : K[X]) * a2 * f * H -
          (19440 : K[X]) * a2 * g1 ^ 2 * H +
          Polynomial.C κ *
            ((5184 : K[X]) * a3 * g1 * H + (2592 : K[X]) * f ^ 2 * H -
              (1728 : K[X]) * f * g1 ^ 2 * H +
              (240 : K[X]) * g1 ^ 4 * H +
              (15552 : K[X]) * a2 * H ^ 2) +
          (116640 : K[X]) * a1 * g1 * H ^ 2 -
          Polynomial.C κ₃ * ((216 : K[X]) * f * H ^ 2) +
          (174960 : K[X]) * a0 * H ^ 3 =
        Polynomial.C κ₅ * H ^ 3)
    {a : K} (ha : H.eval a = 0) :
    729 * a3.eval a ^ 2 - 486 * a3.eval a * f.eval a * g1.eval a -
        81 * f.eval a ^ 3 + 108 * a3.eval a * g1.eval a ^ 3 +
        162 * f.eval a ^ 2 * g1.eval a ^ 2 -
        63 * f.eval a * g1.eval a ^ 4 + 7 * g1.eval a ^ 6 = 0 := by
  have hev := congrArg (fun t : K[X] => t.eval a) hcore
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hev
  rw [ha] at hev
  linear_combination (80⁻¹ : K) * hev

/-- In the nonsquare chamber the sextic block vanishes at both simple
roots of `H`, so `H` divides it: the quotient `t` of the consumed
degree-`9` row. -/
theorem alignedNonsquareSixth_dvd_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 f a0 a1 a2 a3 b4 : k[X]} {κ κ₃ κ₅ : k}
    (hdeg : H.natDegree = 2) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hcore :
      (58320 : k[X]) * a3 ^ 2 - (38880 : k[X]) * a3 * f * g1 -
          (6480 : k[X]) * f ^ 3 + (8640 : k[X]) * a3 * g1 ^ 3 +
          (12960 : k[X]) * f ^ 2 * g1 ^ 2 -
          (5040 : k[X]) * f * g1 ^ 4 + (560 : k[X]) * g1 ^ 6 -
          (104976 : k[X]) * b4 * H + (116640 : k[X]) * a2 * f * H -
          (19440 : k[X]) * a2 * g1 ^ 2 * H +
          Polynomial.C κ *
            ((5184 : k[X]) * a3 * g1 * H + (2592 : k[X]) * f ^ 2 * H -
              (1728 : k[X]) * f * g1 ^ 2 * H +
              (240 : k[X]) * g1 ^ 4 * H +
              (15552 : k[X]) * a2 * H ^ 2) +
          (116640 : k[X]) * a1 * g1 * H ^ 2 -
          Polynomial.C κ₃ * ((216 : k[X]) * f * H ^ 2) +
          (174960 : k[X]) * a0 * H ^ 3 =
        Polynomial.C κ₅ * H ^ 3) :
    ∃ t : k[X],
      (58320 : k[X]) * a3 ^ 2 - (38880 : k[X]) * a3 * f * g1 -
          (6480 : k[X]) * f ^ 3 + (8640 : k[X]) * a3 * g1 ^ 3 +
          (12960 : k[X]) * f ^ 2 * g1 ^ 2 -
          (5040 : k[X]) * f * g1 ^ 4 + (560 : k[X]) * g1 ^ 6 =
        H * t := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hroot : ∀ a : k, H.eval a = 0 →
      ((58320 : k[X]) * a3 ^ 2 - (38880 : k[X]) * a3 * f * g1 -
        (6480 : k[X]) * f ^ 3 + (8640 : k[X]) * a3 * g1 ^ 3 +
        (12960 : k[X]) * f ^ 2 * g1 ^ 2 -
        (5040 : k[X]) * f * g1 ^ 4 +
        (560 : k[X]) * g1 ^ 6).eval a = 0 := by
    intro a ha
    have htie := alignedNonsquareSixth_rootTie_610 hcore ha
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
    linear_combination (80 : k) * htie
  obtain ⟨t, ht⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hroot
  exact ⟨t, ht⟩

/-- Simple-root form of the consumed degree-`9` row in the nonsquare
chamber: with the quotient `t` the quartic coefficient is solved — the
`H`-free part is inhomogeneous in `t`. -/
theorem alignedNonsquareSixth_solved_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f t a0 a1 a2 a3 b4 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0)
    (hcore :
      (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f * g1 -
          (6480 : K[X]) * f ^ 3 + (8640 : K[X]) * a3 * g1 ^ 3 +
          (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
          (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 -
          (104976 : K[X]) * b4 * H + (116640 : K[X]) * a2 * f * H -
          (19440 : K[X]) * a2 * g1 ^ 2 * H +
          Polynomial.C κ *
            ((5184 : K[X]) * a3 * g1 * H + (2592 : K[X]) * f ^ 2 * H -
              (1728 : K[X]) * f * g1 ^ 2 * H +
              (240 : K[X]) * g1 ^ 4 * H +
              (15552 : K[X]) * a2 * H ^ 2) +
          (116640 : K[X]) * a1 * g1 * H ^ 2 -
          Polynomial.C κ₃ * ((216 : K[X]) * f * H ^ 2) +
          (174960 : K[X]) * a0 * H ^ 3 =
        Polynomial.C κ₅ * H ^ 3)
    (ht : (58320 : K[X]) * a3 ^ 2 - (38880 : K[X]) * a3 * f * g1 -
        (6480 : K[X]) * f ^ 3 + (8640 : K[X]) * a3 * g1 ^ 3 +
        (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
        (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 = H * t) :
    (104976 : K[X]) * b4 =
      t + (116640 : K[X]) * a2 * f - (19440 : K[X]) * a2 * g1 ^ 2 +
        Polynomial.C κ *
          ((5184 : K[X]) * a3 * g1 + (2592 : K[X]) * f ^ 2 -
            (1728 : K[X]) * f * g1 ^ 2 + (240 : K[X]) * g1 ^ 4 +
            (15552 : K[X]) * a2 * H) +
        (116640 : K[X]) * a1 * g1 * H -
        Polynomial.C κ₃ * ((216 : K[X]) * f * H) +
        (174960 : K[X]) * a0 * H ^ 2 - Polynomial.C κ₅ * H ^ 2 := by
  have h2 : H * ((104976 : K[X]) * b4 - t - (116640 : K[X]) * a2 * f +
      (19440 : K[X]) * a2 * g1 ^ 2 -
      Polynomial.C κ *
        ((5184 : K[X]) * a3 * g1 + (2592 : K[X]) * f ^ 2 -
          (1728 : K[X]) * f * g1 ^ 2 + (240 : K[X]) * g1 ^ 4 +
          (15552 : K[X]) * a2 * H) -
      (116640 : K[X]) * a1 * g1 * H +
      Polynomial.C κ₃ * ((216 : K[X]) * f * H) -
      (174960 : K[X]) * a0 * H ^ 2 + Polynomial.C κ₅ * H ^ 2) = 0 := by
    linear_combination ht - hcore
  have h3 := (mul_eq_zero.mp h2).resolve_left hH
  linear_combination h3

/-! ## Source-facing sixth-row packets -/

/-- Source-facing weight-fifteen integral of a normalized aligned
scale-two `(6,10)` source: the degree-`9` row is consumed into the
chamber-free `G = κ₅ H¹⁵` on top of the previous aligned packet. -/
theorem normalized610ScaleTwo_alignedSixthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ κ₅ : K),
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
          Polynomial.C κ₅ * H ^ 15 := by
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
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, aligned_q9_solved_610 haligned, hM, hD2,
    hE, hF2, hG⟩

/-- Exact square-chamber sixth packet of a normalized aligned scale-two
`(6,10)` source: the second-order kill `p₄ = h₀² f₂` (resolving the
fifth-face residual branch), the sextic tie on `p₃`, the outright
solved `q₄` and upgraded outright solved `q₅`, and the factored defect
relations pinning `μ`, `κ₃`, `ν`, `κ₅`. -/
theorem normalized610ScaleTwo_alignedSixthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ ν κ₅ : K) (w1 f2 s : K[X]),
      p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (58320 : K[X]) * p.coeff 3 ^ 2 -
            (38880 : K[X]) * p.coeff 3 * f2 * w1 -
            (6480 : K[X]) * f2 ^ 3 +
            (8640 : K[X]) * p.coeff 3 * w1 ^ 3 +
            (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
            (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 =
          h0 ^ 2 * s ∧
        (104976 : K[X]) * q.coeff 4 =
          (174960 : K[X]) * p.coeff 0 * h0 ^ 4 +
            (116640 : K[X]) * p.coeff 1 * w1 * h0 ^ 2 +
            (116640 : K[X]) * p.coeff 2 * f2 -
            (19440 : K[X]) * p.coeff 2 * w1 ^ 2 + s +
            Polynomial.C κ *
              ((15552 : K[X]) * p.coeff 2 * h0 ^ 2 +
                (5184 : K[X]) * p.coeff 3 * w1 +
                (2592 : K[X]) * f2 ^ 2 -
                (1728 : K[X]) * f2 * w1 ^ 2 + (240 : K[X]) * w1 ^ 4) -
            Polynomial.C μ *
              ((1512 : K[X]) * p.coeff 3 * h0 +
                (252 : K[X]) * f2 * w1 * h0 -
                (35 : K[X]) * w1 ^ 3 * h0) -
            Polynomial.C κ₃ * ((216 : K[X]) * f2 * h0 ^ 2) -
            Polynomial.C ν * ((15 : K[X]) * w1 * h0 ^ 3) -
            Polynomial.C κ₅ * h0 ^ 4 ∧
        (5832 : K[X]) * q.coeff 5 =
          (9720 : K[X]) * p.coeff 1 * h0 ^ 4 +
            (6480 : K[X]) * p.coeff 2 * w1 * h0 ^ 2 +
            (6480 : K[X]) * p.coeff 3 * f2 -
            (1080 : K[X]) * p.coeff 3 * w1 ^ 2 -
            (1080 : K[X]) * f2 ^ 2 * w1 + (480 : K[X]) * f2 * w1 ^ 3 -
            (56 : K[X]) * w1 ^ 5 +
            Polynomial.C κ *
              ((864 : K[X]) * p.coeff 3 * h0 ^ 2 +
                (288 : K[X]) * f2 * w1 * h0 ^ 2 -
                (32 : K[X]) * w1 ^ 3 * h0 ^ 2) -
            Polynomial.C μ *
              ((84 : K[X]) * f2 * h0 ^ 3 + (7 : K[X]) * w1 ^ 2 * h0 ^ 3) -
            Polynomial.C κ₃ * ((12 : K[X]) * w1 * h0 ^ 4) -
            Polynomial.C ν * h0 ^ 5 ∧
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
          Polynomial.C κ₅ * H ^ 15 := by
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
  obtain ⟨s, htie6, hq4⟩ := alignedSquareSixth_tie_610 hcore2
  have hp4f2 : p.coeff 4 = h0 ^ 2 * f2 := by rw [hf1, hf2]; ring
  have hq5s := alignedSquareSixth_q5Upgrade_610 hh0 hf2 hq5
  exact ⟨κ, μ, κ₃, ν, κ₅, w1, f2, s, hp5w1, hp4f2, htie6, hq4, hq5s,
    hD, hE4, hF, hG⟩

/-- Exact nonsquare-chamber sixth packet of a normalized aligned
scale-two `(6,10)` source: the sextic block divisible by `H` with
quotient `t`, the quartic coefficient `q₄` solved against `t`, and the
factored defect relations (`D = 0`, `F = 0`, `E = κ₃ H¹⁰`,
`G = κ₅ H¹⁵`). -/
theorem normalized610ScaleTwo_alignedSixthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ : K) (g1 f t : K[X]),
      p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (58320 : K[X]) * p.coeff 3 ^ 2 -
            (38880 : K[X]) * p.coeff 3 * f * g1 -
            (6480 : K[X]) * f ^ 3 +
            (8640 : K[X]) * p.coeff 3 * g1 ^ 3 +
            (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
            (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 =
          H * t ∧
        (104976 : K[X]) * q.coeff 4 =
          t + (116640 : K[X]) * p.coeff 2 * f -
            (19440 : K[X]) * p.coeff 2 * g1 ^ 2 +
            Polynomial.C κ *
              ((5184 : K[X]) * p.coeff 3 * g1 +
                (2592 : K[X]) * f ^ 2 - (1728 : K[X]) * f * g1 ^ 2 +
                (240 : K[X]) * g1 ^ 4 +
                (15552 : K[X]) * p.coeff 2 * H) +
            (116640 : K[X]) * p.coeff 1 * g1 * H -
            Polynomial.C κ₃ * ((216 : K[X]) * f * H) +
            (174960 : K[X]) * p.coeff 0 * H ^ 2 -
            Polynomial.C κ₅ * H ^ 2 ∧
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
          Polynomial.C κ₅ * H ^ 15 := by
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
  have hq4 := alignedNonsquareSixth_solved_610 hH hcore6 ht
  exact ⟨κ, κ₃, κ₅, g1, f, t, hp5, hf, ht, hq4, hD0, hE4, hF0, hG⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`9`
aligned row (solved forms of `q₄` and `q₅` are in the two chamber
packets above).  Neither chamber is excluded and no closure is
claimed. -/
theorem normalized610ScaleTwo_alignedSixthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (w1 f2 s : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (58320 : K[X]) * p.coeff 3 ^ 2 -
              (38880 : K[X]) * p.coeff 3 * f2 * w1 -
              (6480 : K[X]) * f2 ^ 3 +
              (8640 : K[X]) * p.coeff 3 * w1 ^ 3 +
              (12960 : K[X]) * f2 ^ 2 * w1 ^ 2 -
              (5040 : K[X]) * f2 * w1 ^ 4 + (560 : K[X]) * w1 ^ 6 =
            h0 ^ 2 * s) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (58320 : K[X]) * p.coeff 3 ^ 2 -
              (38880 : K[X]) * p.coeff 3 * f * g1 -
              (6480 : K[X]) * f ^ 3 +
              (8640 : K[X]) * p.coeff 3 * g1 ^ 3 +
              (12960 : K[X]) * f ^ 2 * g1 ^ 2 -
              (5040 : K[X]) * f * g1 ^ 4 + (560 : K[X]) * g1 ^ 6 =
            H * t) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedSixthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, w1, f2, s, hp5, hp4, htie, _hq4, _hq5,
      _hD, _hE, _hF, _hG⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, w1, f2, s, hp5, hp4, htie⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedSixthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, g1, f, t, hp5, hp4, ht, _hq4, _hD0, _hE, _hF0,
      _hG⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t, hp5, hp4, ht⟩

/-- Root data of the consumed degree-`9` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇` vanishes, and the new
row extends the COMMON jet by `p₄(a) = 0` and `q₆(a) = 0` in both
chambers — in the square chamber the fifth-face residual branch is
resolved into the second-order kill `p₄ = h₀² f₂`, with the sextic
root tie on `p₃` and the outright `q₅` root relation; in the nonsquare
chamber the same sextic root tie holds at the root. -/
theorem normalized610ScaleTwo_alignedSixthFace_rootData
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
      ((∃ h0 w1 f2 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          729 * (p.coeff 3).eval a ^ 2 -
              486 * (p.coeff 3).eval a * f2.eval a * w1.eval a -
              81 * f2.eval a ^ 3 +
              108 * (p.coeff 3).eval a * w1.eval a ^ 3 +
              162 * f2.eval a ^ 2 * w1.eval a ^ 2 -
              63 * f2.eval a * w1.eval a ^ 4 +
              7 * w1.eval a ^ 6 = 0 ∧
          5832 * (q.coeff 5).eval a =
            6480 * (p.coeff 3).eval a * f2.eval a -
              1080 * (p.coeff 3).eval a * w1.eval a ^ 2 -
              1080 * f2.eval a ^ 2 * w1.eval a +
              480 * f2.eval a * w1.eval a ^ 3 -
              56 * w1.eval a ^ 5) ∨
        (∃ g1 f : K[X], p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f ∧
          729 * (p.coeff 3).eval a ^ 2 -
              486 * (p.coeff 3).eval a * f.eval a * g1.eval a -
              81 * f.eval a ^ 3 +
              108 * (p.coeff 3).eval a * g1.eval a ^ 3 +
              162 * f.eval a ^ 2 * g1.eval a ^ 2 -
              63 * f.eval a * g1.eval a ^ 4 +
              7 * g1.eval a ^ 6 = 0)) := by
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
    have hpacket6 :=
      normalized610ScaleTwo_alignedSixthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket6
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, w1, f2, s, hp5w1, hp4f2, htie6, _hq4,
      hq5s, _hD, _hE, _hF, _hG⟩ := hpacket6
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
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, hh0, hHsq, hroot, hp5w1, hp4f2, ?_, ?_⟩⟩
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
    · have hev := congrArg (fun t : K[X] => t.eval a) htie6
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      linear_combination (80⁻¹ : K) * hev
    · have hev := congrArg (fun t : K[X] => t.eval a) hq5s
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      linear_combination hev
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, κ₃A, g1', f', _hp5', hq9, hq8, hq7, _hf', hq6, _hq5',
      _hD0', _hE', _hF0'⟩ := hpacket5
    have hpacket6 :=
      normalized610ScaleTwo_alignedSixthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket6
    obtain ⟨κB, κ₃B, κ₅B, g1, f, t, hp5, hp4, ht, _hq4, _hD0, _hE,
      _hF0, _hG⟩ := hpacket6
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, hp5, hp4, ?_⟩⟩
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
    · rw [hp4, Polynomial.eval_mul, hroot, zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (486 : K) ≠ 0)
    · have hev := congrArg (fun s : K[X] => s.eval a) ht
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      linear_combination (80⁻¹ : K) * hev

#print axioms alignedSixthCoefficientJacobianRow_610
#print axioms alignedSixthDefect_weightedDerivative_identity_610
#print axioms alignedSixthDefectRow_eq_zero_610
#print axioms alignedSixthDefectPowerRelation_610
#print axioms alignedSquareSixth_core_610
#print axioms alignedSquareSixth_descent_610
#print axioms alignedSquareSixth_tie_610
#print axioms alignedSquareSixth_q5Upgrade_610
#print axioms alignedNonsquareSixth_core_610
#print axioms alignedNonsquareSixth_rootTie_610
#print axioms alignedNonsquareSixth_dvd_610
#print axioms alignedNonsquareSixth_solved_610
#print axioms normalized610ScaleTwo_alignedSixthFace_packet
#print axioms normalized610ScaleTwo_alignedSixthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedSixthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedSixthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedSixthFace_rootData

end Max11DegreeRoutes
