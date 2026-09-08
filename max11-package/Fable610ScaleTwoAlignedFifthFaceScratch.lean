import Fable610ScaleTwoAlignedFourthFaceScratch

/-! # Fifth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedFourthFaceScratch` consumed the degree-`11`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0`: the
chamber-free weight-ten integral `E = κ₃ H¹⁰` of the fourth defect,
with the square-chamber quartic tie `270 p₄² - 90 p₄ w² + 10 w⁴ = h₀² r`
and the nonsquare divisibility `p₄ = H f`.  This file consumes the next
unused aligned row, the degree-`10` Jacobian coefficient — the first
row that sees `p₁` and `q₅`.

At the common source level, modulo the face `N = 0`, the consumed
degree-`13` relation `C = 9 q₈ H - 15 p₄ H³ - 5 p₅² - κ H⁵ = 0`, the
consumed degree-`12` row `2 H D' - 15 D H' = 0`, and the consumed
degree-`11` row `H E' - 10 E H' = 0`, the degree-`10` row is the
weighted derivative of the cleared fifth defect

`F = 9720 p₁ H¹² - 5832 q₅ H¹⁰ + 6480 p₂ p₅ H⁹ + 6480 p₃ p₄ H⁹
  - 1080 p₃ p₅² H⁶ - 1080 p₄² p₅ H⁶ + 480 p₄ p₅³ H³ - 56 p₅⁵
  + κ (864 p₃ H¹¹ + 288 p₄ p₅ H⁸ - 32 p₅³ H⁵)
  - (84 p₄ H³ + 7 p₅²) D - 12 p₅ E`,

kept in factored form through the third defect `D` and the fourth
defect `E`, via the exact multiplier identity

`1944 H⁸ · row₁₀[p₆ = H³, q₁₀ = H⁵] = (2 H F' - 25 F H')
  - 5832 H⁸ p₂' N + 1296 H⁸ p₂ N' + (1728 H⁷ p₃' + 648 H⁶ p₃ H') C
  - 648 H⁷ p₃ C' + (132 p₄ H³ + 77 p₅²)(2 H D' - 15 D H')
  + 44 p₅ (H E' - 10 E H')`.

On the aligned face every right-hand correction vanishes, so
`2 H F' = 25 F H'` and the squared weight-twenty-five first integral

`F² = κ₄ H²⁵`

holds for a preserved constant `κ₄`.  The odd exponent splits honestly
on the chambers of the previous packets:

* square chamber `H = h₀²`, `p₅ = h₀³ w`, `D = μ h₀¹⁵`, `E = κ₃ h₀²⁰`:
  the integral has a polynomial square root `F = ν h₀²⁵` with
  `ν² = κ₄`.  Cancelling `h₀¹⁵` leaves the chamber core, whose
  `h₀`-free part is the quintic `-8 w (135 p₄² - 60 p₄ w² + 7 w⁴)`.
  At the root of `h₀` the quintic factor combines with the fourth-row
  quartic tie `27 p₄(a)² - 9 p₄(a) w(a)² + w(a)⁴ = 0`: the resultant
  elimination (`(135 x² - 60 x y² + 7 y⁴) - 5 (27 x² - 9 x y² + y⁴)
  = -y² (15 x - 2 y²)` and `63 y⁴ = 225 (27 x² - 9 x y² + y⁴)
  + (405 x - 81 y²)(2 y² - 15 x)`) kills BOTH: `w(a) = 0` and
  `p₄(a) = 0`.  The linear-root transfer upgrades the chamber to the
  new divisibilities `w = h₀ w₁` (so `p₅ = h₀⁴ w₁`) and `p₄ = h₀ f₁`
  — resolving the fourth-row quartic tie into clean vanishing — and
  the quintic row is solved as the peeled relation
  `5832 q₅ h₀² = 9720 p₁ h₀⁶ + 6480 p₂ w₁ h₀⁴ + 6480 p₃ f₁ h₀
  - 1080 p₃ w₁² h₀² - 1080 f₁² w₁ + 480 f₁ w₁³ h₀ - 56 w₁⁵ h₀²
  + κ (864 p₃ h₀⁴ + 288 f₁ w₁ h₀³ - 32 w₁³ h₀⁴)
  - μ (84 f₁ h₀⁴ + 7 w₁² h₀⁵) - κ₃ (12 w₁ h₀⁶) - ν h₀⁷`.  At the root
  the peeled row leaves the honest residual branch
  `w₁(a) = 0 ∨ f₁(a) = 0` (from the `h₀`-free term `-1080 f₁² w₁`);
  `q₅` itself is not forced to vanish.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `E = κ₃ H¹⁰`: the odd exponent
  forces `κ₄ = 0` and `F = 0` identically; cancelling `H¹⁰` solves the
  quintic coefficient outright:
  `5832 q₅ = 9720 p₁ H² + 6480 p₂ g₁ H + 6480 p₃ f - 1080 p₃ g₁²
  - 1080 f² g₁ + 480 f g₁³ - 56 g₁⁵
  + κ (864 p₃ H + 288 f g₁ H - 32 g₁³ H) - κ₃ (12 g₁ H²)`.
  Unlike the previous nonsquare rows there is NO `H` factor: at a root
  of `H` the row leaves the honest inhomogeneous root relation
  `5832 q₅(a) = 6480 p₃(a) f(a) - 1080 p₃(a) g₁(a)² - 1080 f(a)² g₁(a)
  + 480 f(a) g₁(a)³ - 56 g₁(a)⁵`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, `dvd_of_sq_dvd_sq_poly`,
and `linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w = 0`, `w₁ = 0`, `f₁ = 0`, `g₁ = 0`, `f = 0`, `r = 0`, `κ = 0`,
`μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₄ = 0`) are not excluded, and the
constants `κ`, `κ₂ = μ²`, `κ₃`, `κ₄ = ν²` are preserved where not
forced.  The next unused Keller row on the aligned face is the
degree-`9` Jacobian coefficient, the first row that sees `p₀` and
`q₄` (expected weight-fifteen defect, even exponent, chamber-free).
No total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`10` Keller coefficient on the aligned face -/

/-- The fifth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`10` Jacobian coefficient, the first
aligned row that sees `p₁` and `q₅`. -/
theorem alignedFifthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 9).derivative +
        p.coeff 1 * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 10) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (10 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 10 :
      Finset (ℕ × ℕ)) =
      ({(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4),
        (7, 3), (8, 2), (9, 1),
        (10, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
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
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned fifth defect -/

/-- Cleared fifth defect of the degree-`10` aligned `(6,10)` row, kept
in factored form through the third defect `D` and the fourth defect
`E`:
`F = 9720 p₁ H¹² - 5832 q₅ H¹⁰ + 6480 p₂ p₅ H⁹ + 6480 p₃ p₄ H⁹
- 1080 p₃ p₅² H⁶ - 1080 p₄² p₅ H⁶ + 480 p₄ p₅³ H³ - 56 p₅⁵
+ κ (864 p₃ H¹¹ + 288 p₄ p₅ H⁸ - 32 p₅³ H⁵) - (84 p₄ H³ + 7 p₅²) D
- 12 p₅ E`.  On the aligned face its square is a polynomial first
integral of weight twenty-five. -/
def alignedFifthDefect610 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (9720 : K[X]) * a1 * H ^ 12 - (5832 : K[X]) * b5 * H ^ 10 +
    (6480 : K[X]) * a2 * a5 * H ^ 9 + (6480 : K[X]) * a3 * a4 * H ^ 9 -
    (1080 : K[X]) * a3 * a5 ^ 2 * H ^ 6 -
    (1080 : K[X]) * a4 ^ 2 * a5 * H ^ 6 +
    (480 : K[X]) * a4 * a5 ^ 3 * H ^ 3 - (56 : K[X]) * a5 ^ 5 +
    Polynomial.C κ *
      ((864 : K[X]) * a3 * H ^ 11 + (288 : K[X]) * a4 * a5 * H ^ 8 -
        (32 : K[X]) * a5 ^ 3 * H ^ 5) -
    ((84 : K[X]) * a4 * H ^ 3 + (7 : K[X]) * a5 ^ 2) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (12 : K[X]) * a5 * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ

set_option maxHeartbeats 800000000 in
/-- Exact combination of the degree-`10` Jacobian expression with the
weighted derivative of `F`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13`,
degree-`12`, and degree-`11` rows. -/
theorem alignedFifthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a1 a2 a3 a4 a5 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (1944 : K[X]) * H ^ 8 *
        ((H ^ 3).derivative * (b5 * (5 : K[X])) +
          a5.derivative * (b6 * (6 : K[X])) +
          a4.derivative * (b7 * (7 : K[X])) +
          a3.derivative * (b8 * (8 : K[X])) +
          a2.derivative * (b9 * (9 : K[X])) +
          a1.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b5.derivative +
          (a5 * (5 : K[X])) * b6.derivative +
          (a4 * (4 : K[X])) * b7.derivative +
          (a3 * (3 : K[X])) * b8.derivative +
          (a2 * (2 : K[X])) * b9.derivative +
          a1 * (H ^ 5).derivative)) =
      ((2 : K[X]) * H *
          (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ).derivative -
        (25 : K[X]) * alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ *
          H.derivative) -
        (5832 : K[X]) * H ^ 8 * a2.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) +
        (1296 : K[X]) * H ^ 8 * a2 *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9).derivative +
        ((1728 : K[X]) * H ^ 7 * a3.derivative +
            (648 : K[X]) * H ^ 6 * a3 * H.derivative) *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) -
        (648 : K[X]) * H ^ 7 * a3 *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5).derivative +
        ((132 : K[X]) * a4 * H ^ 3 + (77 : K[X]) * a5 ^ 2) *
          ((2 : K[X]) * H *
              (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
            (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
              H.derivative) +
        (44 : K[X]) * a5 *
          (H * (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative -
            (10 : K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ *
              H.derivative) := by
  simp only [alignedFifthDefect610, alignedFourthDefect610,
    alignedThirdDefect610, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero,
    zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face, with the consumed degree-`13`, degree-`12`,
and degree-`11` rows, the degree-`10` row is the weighted derivative
`2 H F' - 25 F H' = 0`. -/
theorem alignedFifthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H *
        (alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
          κ).derivative -
      (25 : K[X]) *
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedFifthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC5, hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2] at hrow
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
  have hid := alignedFifthDefect_weightedDerivative_identity_610
    H (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
    (q.coeff 5) (q.coeff 6) (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hDrow, hErow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-twenty-five polynomial first integral of the aligned
`(6,10)` fifth defect: `F² = κ₄ H²⁵`. -/
theorem alignedFifthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₄ : K,
      alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
          κ ^ 2 =
        Polynomial.C κ₄ * H ^ 25 := by
  let F : K[X] :=
    alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * F.derivative -
        (25 : K[X]) * F * H.derivative = 0 := by
    simpa only [F] using
      alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC25 : Polynomial.C (25 : K) = (25 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (F ^ 2) (H ^ 25) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      F ^ 2 * (Polynomial.C (25 : K) * H ^ (25 - 1) * H.derivative) -
          Polynomial.C (2 : K) * F ^ (2 - 1) * F.derivative * H ^ 25 =
          F * H ^ 24 *
            (Polynomial.C (25 : K) * F * H.derivative -
              Polynomial.C (2 : K) * H * F.derivative) := by
        ring
      _ = 0 := by
        rw [hC25, hC2]
        have hfac :
            (25 : K[X]) * F * H.derivative -
              (2 : K[X]) * H * F.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 25 hH) hW

/-! ## Square chamber -/

/-- In the square chamber the weight-twenty-five integral has a
polynomial square root: `F = ν h₀²⁵` with `ν² = κ₄`.  The constant `ν`
is preserved, not cleared. -/
theorem alignedSquareFifth_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a1 a2 a3 a4 a5 b5 b6 b7 : K[X]} {κ κ₄ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hF2 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₄ * H ^ 25) :
    ∃ ν : K, ν ^ 2 = κ₄ ∧
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
        Polynomial.C ν * h0 ^ 25 := by
  set F : K[X] := alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ
  have hdvd : (h0 ^ 25) ^ 2 ∣ F ^ 2 := by
    refine ⟨Polynomial.C κ₄, ?_⟩
    rw [hF2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₄ := by
    have h50 := hF2
    rw [hG, hHsq] at h50
    apply mul_left_cancel₀ (pow_ne_zero 50 hh0)
    linear_combination h50
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₄
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν, ?_, ?_⟩
  · have hCν : Polynomial.C (ν ^ 2) = Polynomial.C κ₄ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

/-- Cleared square-core form of the fifth defect relation: cancelling
`h₀¹⁵` from `F = ν h₀²⁵` on `p₅ = h₀³ w`, `D = μ h₀¹⁵`, `E = κ₃ h₀²⁰`
leaves the degree-`10` chamber core with the `h₀`-free quintic
`-1080 p₄² w + 480 p₄ w³ - 56 w⁵`. -/
theorem alignedSquareFifth_core_610 {K : Type*} [Field K] [CharZero K]
    {H h0 w a1 a2 a3 a4 a5 b5 b6 b7 : K[X]} {κ μ κ₃ ν : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp5 : a5 = h0 ^ 3 * w)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25) :
    (9720 : K[X]) * a1 * h0 ^ 9 - (5832 : K[X]) * b5 * h0 ^ 5 +
        (6480 : K[X]) * a2 * w * h0 ^ 6 +
        (6480 : K[X]) * a3 * a4 * h0 ^ 3 -
        (1080 : K[X]) * a3 * w ^ 2 * h0 ^ 3 -
        (1080 : K[X]) * a4 ^ 2 * w + (480 : K[X]) * a4 * w ^ 3 -
        (56 : K[X]) * w ^ 5 +
        Polynomial.C κ *
          ((864 : K[X]) * a3 * h0 ^ 7 + (288 : K[X]) * a4 * w * h0 ^ 4 -
            (32 : K[X]) * w ^ 3 * h0 ^ 4) -
        Polynomial.C μ *
          ((84 : K[X]) * a4 * h0 ^ 6 + (7 : K[X]) * w ^ 2 * h0 ^ 6) -
        Polynomial.C κ₃ * ((12 : K[X]) * w * h0 ^ 8) =
      Polynomial.C ν * h0 ^ 10 := by
  have hF' := hF
  simp only [alignedFifthDefect610] at hF'
  rw [hD, hE, hHsq, hp5] at hF'
  apply mul_left_cancel₀ (pow_ne_zero 15 hh0)
  linear_combination hF'

/-- Root elimination between the fifth-row quintic and the fourth-row
quartic tie: at a common root both `w` and `p₄` are killed. -/
theorem alignedSquareFifth_rootKill_610 {K : Type*} [Field K] [CharZero K]
    {x y : K}
    (h5 : 1080 * x ^ 2 * y - 480 * x * y ^ 3 + 56 * y ^ 5 = 0)
    (h4 : 27 * x ^ 2 - 9 * x * y ^ 2 + y ^ 4 = 0) :
    y = 0 ∧ x = 0 := by
  have h8 : (8 : K) * (y * (135 * x ^ 2 - 60 * x * y ^ 2 + 7 * y ^ 4)) =
      0 := by
    linear_combination h5
  have h8' : y * (135 * x ^ 2 - 60 * x * y ^ 2 + 7 * y ^ 4) = 0 :=
    (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)
  suffices hy : y = 0 by
    refine ⟨hy, ?_⟩
    have hx2 : (27 : K) * x ^ 2 = 0 := by
      linear_combination h4 + (9 * x * y - y ^ 3) * hy
    have hx2' : x ^ 2 = 0 :=
      (mul_eq_zero.mp hx2).resolve_left (by norm_num : (27 : K) ≠ 0)
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2'
  rcases mul_eq_zero.mp h8' with hy | hq
  · exact hy
  · have h3 : y ^ 2 * ((2 : K) * y ^ 2 - 15 * x) = 0 := by
      linear_combination hq - 5 * h4
    rcases mul_eq_zero.mp h3 with hy2 | hlin
    · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hy2
    · have hy4 : (63 : K) * y ^ 4 = 0 := by
        linear_combination (225 : K) * h4 + (405 * x - 81 * y ^ 2) * hlin
      have hy4' : y ^ 4 = 0 :=
        (mul_eq_zero.mp hy4).resolve_left (by norm_num : (63 : K) ≠ 0)
      exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hy4'

/-- Descent of the consumed degree-`10` row in the square chamber: at
the root of `h₀` the chamber core and the fourth-row quartic tie kill
both `w` and `p₄`, so `w = h₀ w₁`, `p₄ = h₀ f₁`, and the quintic row is
solved in peeled form. -/
theorem alignedSquareFifth_descent_610 {K : Type*} [Field K] [CharZero K]
    {h0 w r a1 a2 a3 a4 b5 : K[X]} {κ μ κ₃ ν : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hcore :
      (9720 : K[X]) * a1 * h0 ^ 9 - (5832 : K[X]) * b5 * h0 ^ 5 +
          (6480 : K[X]) * a2 * w * h0 ^ 6 +
          (6480 : K[X]) * a3 * a4 * h0 ^ 3 -
          (1080 : K[X]) * a3 * w ^ 2 * h0 ^ 3 -
          (1080 : K[X]) * a4 ^ 2 * w + (480 : K[X]) * a4 * w ^ 3 -
          (56 : K[X]) * w ^ 5 +
          Polynomial.C κ *
            ((864 : K[X]) * a3 * h0 ^ 7 +
              (288 : K[X]) * a4 * w * h0 ^ 4 -
              (32 : K[X]) * w ^ 3 * h0 ^ 4) -
          Polynomial.C μ *
            ((84 : K[X]) * a4 * h0 ^ 6 + (7 : K[X]) * w ^ 2 * h0 ^ 6) -
          Polynomial.C κ₃ * ((12 : K[X]) * w * h0 ^ 8) =
        Polynomial.C ν * h0 ^ 10)
    (htie : (270 : K[X]) * a4 ^ 2 - (90 : K[X]) * a4 * w ^ 2 +
        (10 : K[X]) * w ^ 4 = h0 ^ 2 * r) :
    ∃ w1 f1 : K[X], w = h0 * w1 ∧ a4 = h0 * f1 ∧
      (5832 : K[X]) * b5 * h0 ^ 2 =
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
          Polynomial.C ν * h0 ^ 7 := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have htie4 :=
    alignedSquareFourth_rootTie_610 htie hroot
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hcore
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have h5 : 1080 * (a4.eval (-(d / c))) ^ 2 * (w.eval (-(d / c))) -
      480 * (a4.eval (-(d / c))) * (w.eval (-(d / c))) ^ 3 +
      56 * (w.eval (-(d / c))) ^ 5 = 0 := by
    linear_combination -hev
  obtain ⟨hyw, hxa4⟩ := alignedSquareFifth_rootKill_610 h5 htie4
  obtain ⟨w1, hw1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w (-(d / c)) hdeg1
      hroot hyw
  obtain ⟨f1, hf1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 a4 (-(d / c)) hdeg1
      hroot hxa4
  refine ⟨w1, f1, hw1, hf1, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
  rw [hw1, hf1] at hcore
  linear_combination -hcore

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the weight-twenty-five
integral forces its constant to vanish, and with it the whole fifth
defect. -/
theorem alignedNonsquareFifth_defect_eq_zero_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a1 a2 a3 a4 a5 b5 b6 b7 : k[X]} {κ κ₄ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hF2 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₄ * H ^ 25) :
    κ₄ = 0 ∧ alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set F : k[X] := alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ
  have hdvd : (H ^ 12) ^ 2 ∣ F ^ 2 := by
    refine ⟨Polynomial.C κ₄ * H, ?_⟩
    rw [hF2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₄ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 24 hH)
    have h24 := hF2
    rw [hG] at h24
    linear_combination h24
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₄ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk4 : κ₄ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hFzero : F = 0 := by
    have hsq : F ^ 2 = 0 := by
      rw [hF2, hk4]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk4, hFzero⟩

/-- Simple-root form of the consumed degree-`10` row in the nonsquare
chamber: with `p₅ = H² g₁` and `p₄ = H f` the quintic coefficient is
solved outright — with NO overall `H` factor. -/
theorem alignedNonsquareFifth_solved_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f a1 a2 a3 a4 a5 b5 b6 b7 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0) :
    (5832 : K[X]) * b5 =
      (9720 : K[X]) * a1 * H ^ 2 + (6480 : K[X]) * a2 * g1 * H +
        (6480 : K[X]) * a3 * f - (1080 : K[X]) * a3 * g1 ^ 2 -
        (1080 : K[X]) * f ^ 2 * g1 + (480 : K[X]) * f * g1 ^ 3 -
        (56 : K[X]) * g1 ^ 5 +
        Polynomial.C κ *
          ((864 : K[X]) * a3 * H + (288 : K[X]) * f * g1 * H -
            (32 : K[X]) * g1 ^ 3 * H) -
        Polynomial.C κ₃ * ((12 : K[X]) * g1 * H ^ 2) := by
  have hF' := hF0
  simp only [alignedFifthDefect610] at hF'
  rw [hD0, hE, hg1, hf] at hF'
  apply mul_left_cancel₀ (pow_ne_zero 10 hH)
  linear_combination -hF'

/-! ## Source-facing fifth-row packets -/

/-- Source-facing squared weight-twenty-five integral of a normalized
aligned scale-two `(6,10)` source: the degree-`10` row is consumed into
`F² = κ₄ H²⁵` on top of the previous aligned packet. -/
theorem normalized610ScaleTwo_alignedFifthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ : K),
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
          Polynomial.C κ₄ * H ^ 25 := by
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
  exact ⟨κ, κ₂, κ₃, κ₄, aligned_q9_solved_610 haligned, hM, hD2, hE, hF2⟩

/-- Exact square-chamber fifth packet of a normalized aligned scale-two
`(6,10)` source: the previous packet plus the square root `F = ν h₀²⁵`,
the new divisibilities `w = h₀ w₁` (so `p₅ = h₀⁴ w₁`) and `p₄ = h₀ f₁`
— resolving the fourth-row quartic tie into clean vanishing at the root
— and the peeled solved quintic row. -/
theorem normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ ν : K) (w r w1 f1 : K[X]),
      p.coeff 5 = h0 ^ 3 * w ∧
        q.coeff 9 = Polynomial.C (5 / 3 : K) * w * h0 ^ 7 ∧
        (9 : K[X]) * q.coeff 8 =
          h0 ^ 4 * ((5 : K[X]) * w ^ 2 + (15 : K[X]) * p.coeff 4 +
            Polynomial.C κ * h0 ^ 4) ∧
        (81 : K[X]) * q.coeff 7 =
          h0 * ((135 : K[X]) * p.coeff 3 * h0 ^ 3 +
            (90 : K[X]) * p.coeff 4 * w - (5 : K[X]) * w ^ 3 +
            Polynomial.C κ * ((12 : K[X]) * w * h0 ^ 4) -
            Polynomial.C μ * h0 ^ 6) ∧
        (270 : K[X]) * p.coeff 4 ^ 2 - (90 : K[X]) * p.coeff 4 * w ^ 2 +
            (10 : K[X]) * w ^ 4 = h0 ^ 2 * r ∧
        (486 : K[X]) * q.coeff 6 =
          (810 : K[X]) * p.coeff 2 * h0 ^ 4 +
            (540 : K[X]) * p.coeff 3 * w * h0 + r +
            Polynomial.C κ *
              ((72 : K[X]) * p.coeff 4 * h0 ^ 2 +
                (12 : K[X]) * w ^ 2 * h0 ^ 2) -
            Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 4) -
            Polynomial.C κ₃ * h0 ^ 6 ∧
        w = h0 * w1 ∧
        p.coeff 4 = h0 * f1 ∧
        (5832 : K[X]) * q.coeff 5 * h0 ^ 2 =
          (9720 : K[X]) * p.coeff 1 * h0 ^ 6 +
            (6480 : K[X]) * p.coeff 2 * w1 * h0 ^ 4 +
            (6480 : K[X]) * p.coeff 3 * f1 * h0 -
            (1080 : K[X]) * p.coeff 3 * w1 ^ 2 * h0 ^ 2 -
            (1080 : K[X]) * f1 ^ 2 * w1 +
            (480 : K[X]) * f1 * w1 ^ 3 * h0 -
            (56 : K[X]) * w1 ^ 5 * h0 ^ 2 +
            Polynomial.C κ *
              ((864 : K[X]) * p.coeff 3 * h0 ^ 4 +
                (288 : K[X]) * f1 * w1 * h0 ^ 3 -
                (32 : K[X]) * w1 ^ 3 * h0 ^ 4) -
            Polynomial.C μ *
              ((84 : K[X]) * f1 * h0 ^ 4 + (7 : K[X]) * w1 ^ 2 * h0 ^ 5) -
            Polynomial.C κ₃ * ((12 : K[X]) * w1 * h0 ^ 6) -
            Polynomial.C ν * h0 ^ 7 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ =
          Polynomial.C ν * h0 ^ 25 := by
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
  have hq9 : q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 :=
    aligned_q9_solved_610 haligned
  have hq8 := alignedSquare_q8_solved_610 hh0 hHsq hg hM
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
  obtain ⟨r, htie, hq6⟩ := alignedSquareFourth_tie_610 hcore4
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨ν, _hν2, hF⟩ := alignedSquareFifth_sqrt_610 hh0 hHsq hF2
  have hcore5 := alignedSquareFifth_core_610 hh0 hHsq hp5 hD hE4 hF
  obtain ⟨w1, f1, hw1, hf1, hq5⟩ :=
    alignedSquareFifth_descent_610 hh0 hdeg1 hcore5 htie
  refine ⟨κ, μ, κ₃, ν, w, r, w1, f1, hp5, ?_, ?_, hq7, htie, hq6,
    hw1, hf1, hq5, hF⟩
  · rw [hq9, hg, hgw, hHsq]; ring
  · rw [hq8, hgw]; ring

/-- Exact nonsquare-chamber fifth packet of a normalized aligned
scale-two `(6,10)` source: the previous packet plus the vanished fifth
defect `F = 0` and the solved quintic row — with no overall `H`
factor. -/
theorem normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ : K) (g1 f : K[X]),
      p.coeff 5 = H ^ 2 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 3 : K) * g1 * H ^ 4 ∧
        (9 : K[X]) * q.coeff 8 =
          H ^ 2 * ((5 : K[X]) * H * g1 ^ 2 + (15 : K[X]) * p.coeff 4 +
            Polynomial.C κ * H ^ 2) ∧
        (81 : K[X]) * q.coeff 7 =
          H * ((135 : K[X]) * p.coeff 3 * H +
            (90 : K[X]) * p.coeff 4 * g1 - (5 : K[X]) * H * g1 ^ 3 +
            Polynomial.C κ * ((12 : K[X]) * g1 * H ^ 2)) ∧
        p.coeff 4 = H * f ∧
        (486 : K[X]) * q.coeff 6 =
          H * ((810 : K[X]) * p.coeff 2 * H +
            (540 : K[X]) * p.coeff 3 * g1 + (270 : K[X]) * f ^ 2 -
            (90 : K[X]) * f * g1 ^ 2 + (10 : K[X]) * g1 ^ 4 +
            Polynomial.C κ *
              ((72 : K[X]) * f * H + (12 : K[X]) * g1 ^ 2 * H) -
            Polynomial.C κ₃ * H ^ 2) ∧
        (5832 : K[X]) * q.coeff 5 =
          (9720 : K[X]) * p.coeff 1 * H ^ 2 +
            (6480 : K[X]) * p.coeff 2 * g1 * H +
            (6480 : K[X]) * p.coeff 3 * f -
            (1080 : K[X]) * p.coeff 3 * g1 ^ 2 -
            (1080 : K[X]) * f ^ 2 * g1 + (480 : K[X]) * f * g1 ^ 3 -
            (56 : K[X]) * g1 ^ 5 +
            Polynomial.C κ *
              ((864 : K[X]) * p.coeff 3 * H +
                (288 : K[X]) * f * g1 * H - (32 : K[X]) * g1 ^ 3 * H) -
            Polynomial.C κ₃ * ((12 : K[X]) * g1 * H ^ 2) ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 ∧
        alignedFifthDefect610 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 := by
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
  have hq9 : q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 :=
    aligned_q9_solved_610 haligned
  have hq8 := alignedNonsquare_q8_solved_610 hH hg hM
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
  have hq6 := alignedNonsquareFourth_solved_610 hH hf hcore4
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk4, hF0⟩ :=
    alignedNonsquareFifth_defect_eq_zero_610 hH hHdegree hnsq hF2
  have hq5 := alignedNonsquareFifth_solved_610 hH hp5 hf hD0 hE4 hF0
  refine ⟨κ, κ₃, g1, f, hp5, ?_, ?_, hq7, hf, hq6, hq5, hD0, hE4, hF0⟩
  · rw [hq9, hg, hg1]; ring
  · rw [hq8, hg1]; ring

/-- Honest square/nonsquare chamber split of the consumed degree-`10`
aligned row.  Neither chamber is excluded and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedFifthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₃ ν : K) (w r w1 f1 : K[X]),
        p.coeff 5 = h0 ^ 3 * w ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * w * h0 ^ 7 ∧
          (9 : K[X]) * q.coeff 8 =
            h0 ^ 4 * ((5 : K[X]) * w ^ 2 + (15 : K[X]) * p.coeff 4 +
              Polynomial.C κ * h0 ^ 4) ∧
          (81 : K[X]) * q.coeff 7 =
            h0 * ((135 : K[X]) * p.coeff 3 * h0 ^ 3 +
              (90 : K[X]) * p.coeff 4 * w - (5 : K[X]) * w ^ 3 +
              Polynomial.C κ * ((12 : K[X]) * w * h0 ^ 4) -
              Polynomial.C μ * h0 ^ 6) ∧
          (270 : K[X]) * p.coeff 4 ^ 2 -
              (90 : K[X]) * p.coeff 4 * w ^ 2 +
              (10 : K[X]) * w ^ 4 = h0 ^ 2 * r ∧
          (486 : K[X]) * q.coeff 6 =
            (810 : K[X]) * p.coeff 2 * h0 ^ 4 +
              (540 : K[X]) * p.coeff 3 * w * h0 + r +
              Polynomial.C κ *
                ((72 : K[X]) * p.coeff 4 * h0 ^ 2 +
                  (12 : K[X]) * w ^ 2 * h0 ^ 2) -
              Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 4) -
              Polynomial.C κ₃ * h0 ^ 6 ∧
          w = h0 * w1 ∧
          p.coeff 4 = h0 * f1 ∧
          (5832 : K[X]) * q.coeff 5 * h0 ^ 2 =
            (9720 : K[X]) * p.coeff 1 * h0 ^ 6 +
              (6480 : K[X]) * p.coeff 2 * w1 * h0 ^ 4 +
              (6480 : K[X]) * p.coeff 3 * f1 * h0 -
              (1080 : K[X]) * p.coeff 3 * w1 ^ 2 * h0 ^ 2 -
              (1080 : K[X]) * f1 ^ 2 * w1 +
              (480 : K[X]) * f1 * w1 ^ 3 * h0 -
              (56 : K[X]) * w1 ^ 5 * h0 ^ 2 +
              Polynomial.C κ *
                ((864 : K[X]) * p.coeff 3 * h0 ^ 4 +
                  (288 : K[X]) * f1 * w1 * h0 ^ 3 -
                  (32 : K[X]) * w1 ^ 3 * h0 ^ 4) -
              Polynomial.C μ *
                ((84 : K[X]) * f1 * h0 ^ 4 +
                  (7 : K[X]) * w1 ^ 2 * h0 ^ 5) -
              Polynomial.C κ₃ * ((12 : K[X]) * w1 * h0 ^ 6) -
              Polynomial.C ν * h0 ^ 7) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₃ : K) (g1 f : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * g1 * H ^ 4 ∧
          (9 : K[X]) * q.coeff 8 =
            H ^ 2 * ((5 : K[X]) * H * g1 ^ 2 + (15 : K[X]) * p.coeff 4 +
              Polynomial.C κ * H ^ 2) ∧
          (81 : K[X]) * q.coeff 7 =
            H * ((135 : K[X]) * p.coeff 3 * H +
              (90 : K[X]) * p.coeff 4 * g1 - (5 : K[X]) * H * g1 ^ 3 +
              Polynomial.C κ * ((12 : K[X]) * g1 * H ^ 2)) ∧
          p.coeff 4 = H * f ∧
          (486 : K[X]) * q.coeff 6 =
            H * ((810 : K[X]) * p.coeff 2 * H +
              (540 : K[X]) * p.coeff 3 * g1 + (270 : K[X]) * f ^ 2 -
              (90 : K[X]) * f * g1 ^ 2 + (10 : K[X]) * g1 ^ 4 +
              Polynomial.C κ *
                ((72 : K[X]) * f * H + (12 : K[X]) * g1 ^ 2 * H) -
              Polynomial.C κ₃ * H ^ 2) ∧
          (5832 : K[X]) * q.coeff 5 =
            (9720 : K[X]) * p.coeff 1 * H ^ 2 +
              (6480 : K[X]) * p.coeff 2 * g1 * H +
              (6480 : K[X]) * p.coeff 3 * f -
              (1080 : K[X]) * p.coeff 3 * g1 ^ 2 -
              (1080 : K[X]) * f ^ 2 * g1 + (480 : K[X]) * f * g1 ^ 3 -
              (56 : K[X]) * g1 ^ 5 +
              Polynomial.C κ *
                ((864 : K[X]) * p.coeff 3 * H +
                  (288 : K[X]) * f * g1 * H -
                  (32 : K[X]) * g1 ^ 3 * H) -
              Polynomial.C κ₃ * ((12 : K[X]) * g1 * H ^ 2)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, w, r, w1, f1, hp5, hq9, hq8, hq7, htie, hq6,
      hw1, hf1, hq5, _hF⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₃, ν, w, r, w1, f1, hp5, hq9,
      hq8, hq7, htie, hq6, hw1, hf1, hq5⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6, hq5, _hD0, _hE,
      _hF0⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6, hq5⟩

/-- Root data of the consumed degree-`10` row: at scale two the common
core has a root where the previous jet `p₅, q₉, q₈, q₇` vanishes, and
the new row adds the honest chamber-dependent gain — in the square
chamber the fourth-row quartic tie is resolved into the clean
divisibilities `p₅ = h₀⁴ w₁`, `p₄ = h₀ f₁` (so `p₄(a) = 0`), with the
residual root branch `w₁(a) = 0 ∨ f₁(a) = 0`; in the nonsquare chamber
`p₄(a) = 0`, `q₆(a) = 0`, and the quintic row leaves the inhomogeneous
root relation for `q₅(a)`. -/
theorem normalized610ScaleTwo_alignedFifthFace_rootData
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
      (q.coeff 7).eval a = 0 ∧
      ((∃ h0 w1 f1 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 * f1 ∧
          (p.coeff 4).eval a = 0 ∧
          (w1.eval a = 0 ∨ f1.eval a = 0)) ∨
        ((p.coeff 4).eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
          ∃ g1 f : K[X], p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f ∧
            5832 * (q.coeff 5).eval a =
              6480 * (p.coeff 3).eval a * f.eval a -
                1080 * (p.coeff 3).eval a * g1.eval a ^ 2 -
                1080 * f.eval a ^ 2 * g1.eval a +
                480 * f.eval a * g1.eval a ^ 3 -
                56 * g1.eval a ^ 5)) := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hH
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, w, r, w1, f1, hp5, hq9, hq8, hq7, htie, hq6,
      hw1, hf1, hq5, _hF⟩ := hpacket
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hp5' :
        ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5 =
          h0 ^ 4 * w1 := by
      rw [hp5, hw1]; ring
    have hbranch : w1.eval a = 0 ∨ f1.eval a = 0 := by
      have hev := congrArg (fun t : K[X] => t.eval a) hq5
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      have hprod : f1.eval a ^ 2 * w1.eval a = 0 := by
        linear_combination ((1080 : K)⁻¹) * hev
      rcases mul_eq_zero.mp hprod with hf2 | hw
      · exact Or.inr
          ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hf2)
      · exact Or.inl hw
    refine ⟨a, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f1, hh0, hHsq, hroot, hp5', hf1, ?_, hbranch⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5', Polynomial.eval_mul, Polynomial.eval_pow, hroot,
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
    · rw [hf1, Polynomial.eval_mul, hroot, zero_mul]
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6, hq5, _hD0, _hE,
      _hF0⟩ := hpacket
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hq5root : 5832 *
        ((((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 5).eval
          a) =
        6480 *
            ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
              3).eval a) * f.eval a -
          1080 *
            ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
              3).eval a) * g1.eval a ^ 2 -
          1080 * f.eval a ^ 2 * g1.eval a +
          480 * f.eval a * g1.eval a ^ 3 -
          56 * g1.eval a ^ 5 := by
      have hev := congrArg (fun t : K[X] => t.eval a) hq5
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      linear_combination hev
    refine ⟨a, hroot, ?_, ?_, ?_, ?_,
      Or.inr ⟨?_, ?_, g1, f, hp5, hf, hq5root⟩⟩
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

#print axioms alignedFifthCoefficientJacobianRow_610
#print axioms alignedFifthDefect_weightedDerivative_identity_610
#print axioms alignedFifthDefectRow_eq_zero_610
#print axioms alignedFifthDefectPowerRelation_610
#print axioms alignedSquareFifth_sqrt_610
#print axioms alignedSquareFifth_core_610
#print axioms alignedSquareFifth_rootKill_610
#print axioms alignedSquareFifth_descent_610
#print axioms alignedNonsquareFifth_defect_eq_zero_610
#print axioms alignedNonsquareFifth_solved_610
#print axioms normalized610ScaleTwo_alignedFifthFace_packet
#print axioms normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedFifthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedFifthFace_rootData

end Max11DegreeRoutes
