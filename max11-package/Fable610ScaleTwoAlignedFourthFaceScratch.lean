import Fable610ScaleTwoAlignedThirdFaceScratch

/-! # Fourth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedThirdFaceScratch` consumed the degree-`12`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0`: the squared
weight-fifteen integral `D² = κ₂ H¹⁵` of the third defect
`D = 135 p₃ H⁶ - 81 q₇ H⁴ + 90 p₄ p₅ H³ - 5 p₅³ + 12 κ p₅ H⁵`, with the
square chamber `D = μ h₀¹⁵` and the nonsquare chamber `D = 0`.  This
file consumes the next unused aligned row, the degree-`11` Jacobian
coefficient — the first row that sees `p₂` and `q₆`.

At the common source level, modulo the face `N = 0`, the consumed
degree-`13` relation `C = 9 q₈ H - 15 p₄ H³ - 5 p₅² - κ H⁵ = 0`, and
the consumed degree-`12` row `2 H D' - 15 D H' = 0`, the degree-`11`
row is the weighted derivative of the cleared fourth defect

`E = 810 p₂ H⁹ - 486 q₆ H⁷ + 540 p₃ p₅ H⁶ + 270 p₄² H⁶ - 90 p₄ p₅² H³
  + 10 p₅⁴ + κ (72 p₄ H⁸ + 12 p₅² H⁵) - 7 p₅ D`,

kept in factored form through the third defect `D`, via the exact
multiplier identity

`162 H⁵ · row₁₁[p₆ = H³, q₁₀ = H⁵] = 2 (H E' - 10 E H')
  - 486 H⁵ p₃' N + 162 H⁵ p₃ N' + (144 H⁴ p₄' + 72 H³ p₄ H') C
  - 72 H⁴ p₄ C' + 12 p₅ (2 H D' - 15 D H')`.

On the aligned face every right-hand correction vanishes, so
`H E' = 10 E H'` and the weight-ten polynomial first integral

`E = κ₃ H¹⁰`

holds for a preserved constant `κ₃`.  The exponent is even, so —
unlike the odd weight-fifteen integral of the third row — no square
root of `H` is needed and the integral itself is chamber-free.  The
chambers of the previous packets then specialize the consumed row
honestly:

* square chamber `H = h₀²`, `p₅ = h₀³ w`, `D = μ h₀¹⁵`: cancelling
  `h₀¹²` leaves the chamber core, whose constant part in `h₀` is the
  quartic `270 p₄² - 90 p₄ w² + 10 w⁴`.  The identity forces the new
  quartic tie `270 p₄² - 90 p₄ w² + 10 w⁴ = h₀² r` — the first
  constraint on `p₄` in the aligned tower — and solves the sextic row
  `486 q₆ = 810 p₂ h₀⁴ + 540 p₃ w h₀ + r + κ (72 p₄ h₀² + 12 w² h₀²)
  - 7 μ w h₀⁴ - κ₃ h₀⁶` against the new quotient `r`.  At the root of
  `h₀` the tie reads `27 p₄(a)² - 9 p₄(a) w(a)² + w(a)⁴ = 0`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₅ = H² g₁`, `D = 0`: cancelling `H⁶` leaves a core whose value at
  every root of `H` is `270 p₄(a)²`, so the simple-root transfer gives
  the new divisibility `p₄ = H f` — again the first constraint on `p₄`
  — and the solved sextic row
  `486 q₆ = H (810 p₂ H + 540 p₃ g₁ + 270 f² - 90 f g₁² + 10 g₁⁴
  + κ (72 f H + 12 g₁² H) - κ₃ H²)`; in particular `H ∣ q₆`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` from the `(6,8)` aligned
architecture.  No linear-root descent is needed this time: the square
chamber divisibility `h₀² ∣ (270 p₄² - 90 p₄ w² + 10 w⁴)` comes
directly from the cancelled identity.

No closure is claimed.  Both chambers remain open, the zero branches
(`w = 0`, `g₁ = 0`, `f = 0`, `r = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`) are
not excluded, and the constants `κ`, `κ₂ = μ²`, `κ₃` are preserved
where not forced.  The next unused Keller row on the aligned face is
the degree-`10` Jacobian coefficient, the first row that sees `p₁` and
`q₅`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`11` Keller coefficient on the aligned face -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`11` Jacobian coefficient, the first
aligned row that sees `p₂` and `q₆`.  It is re-derived here directly
from the Keller bracket so that the aligned face keeps its independence
from the nonzero-root chain. -/
theorem alignedFourthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 11) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (11 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 11 :
      Finset (ℕ × ℕ)) =
      ({(0, 11), (1, 10), (2, 9), (3, 8), (4, 7), (5, 6), (6, 5),
        (7, 4), (8, 3), (9, 2), (10, 1),
        (11, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
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
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC7, hC8, hC9, hC10, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned fourth defect -/

/-- Cleared fourth defect of the degree-`11` aligned `(6,10)` row,
kept in factored form through the third defect `D`:
`E = 810 p₂ H⁹ - 486 q₆ H⁷ + 540 p₃ p₅ H⁶ + 270 p₄² H⁶ - 90 p₄ p₅² H³
+ 10 p₅⁴ + κ (72 p₄ H⁸ + 12 p₅² H⁵) - 7 p₅ D`.  On the aligned face it
is a polynomial first integral of weight ten. -/
def alignedFourthDefect610 {K : Type*} [CommRing K]
    (H a2 a3 a4 a5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (810 : K[X]) * a2 * H ^ 9 - (486 : K[X]) * b6 * H ^ 7 +
    (540 : K[X]) * a3 * a5 * H ^ 6 + (270 : K[X]) * a4 ^ 2 * H ^ 6 -
    (90 : K[X]) * a4 * a5 ^ 2 * H ^ 3 + (10 : K[X]) * a5 ^ 4 +
    Polynomial.C κ *
      ((72 : K[X]) * a4 * H ^ 8 + (12 : K[X]) * a5 ^ 2 * H ^ 5) -
    (7 : K[X]) * a5 * alignedThirdDefect610 H a3 a4 a5 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`11` Jacobian expression with the
weighted derivative of `E`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` and
degree-`12` rows. -/
theorem alignedFourthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K] (H a2 a3 a4 a5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (162 : K[X]) * H ^ 5 *
        ((H ^ 3).derivative * (b6 * (6 : K[X])) +
          a5.derivative * (b7 * (7 : K[X])) +
          a4.derivative * (b8 * (8 : K[X])) +
          a3.derivative * (b9 * (9 : K[X])) +
          a2.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b6.derivative +
          (a5 * (5 : K[X])) * b7.derivative +
          (a4 * (4 : K[X])) * b8.derivative +
          (a3 * (3 : K[X])) * b9.derivative +
          (a2 * (2 : K[X])) * (H ^ 5).derivative)) =
      (2 : K[X]) *
          (H * (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative -
            (10 : K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ *
              H.derivative) -
        (486 : K[X]) * H ^ 5 * a3.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) +
        (162 : K[X]) * H ^ 5 * a3 *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9).derivative +
        ((144 : K[X]) * H ^ 4 * a4.derivative +
            (72 : K[X]) * H ^ 3 * a4 * H.derivative) *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) -
        (72 : K[X]) * H ^ 4 * a4 *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5).derivative +
        (12 : K[X]) * a5 *
          ((2 : K[X]) * H *
              (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
            (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
              H.derivative) := by
  simp only [alignedFourthDefect610, alignedThirdDefect610,
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

/-- On the aligned face, with the consumed degree-`13` and degree-`12`
rows, the degree-`11` row is the weighted derivative
`H E' - 10 E H' = 0`. -/
theorem alignedFourthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    H * (alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (10 : K[X]) *
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedFourthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC6, hC7, hC8, hC9, hC10, hC5, hC4, hC3, hC2] at hrow
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
  have hid := alignedFourthDefect_weightedDerivative_identity_610
    H (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6)
    (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hDrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  have h2 : (2 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have hid2 : (2 : K[X]) *
      (H * (alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
        (10 : K[X]) *
          alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative) = 0 := by
    linear_combination -hid
  exact (mul_eq_zero.mp hid2).resolve_left h2

/-- Weight-ten polynomial first integral of the aligned `(6,10)` fourth
defect: `E = κ₃ H¹⁰`.  The even exponent makes the integral chamber-free
— no square root of `H` is required. -/
theorem alignedFourthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₃ : K,
      alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₃ * H ^ 10 := by
  let E : K[X] :=
    alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
      (p.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow : H * E.derivative - (10 : K[X]) * E * H.derivative = 0 := by
    simpa only [E] using
      alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian E (H ^ 10) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      E * (Polynomial.C (10 : K) * H ^ (10 - 1) * H.derivative) -
          E.derivative * H ^ 10 =
          H ^ 9 *
            (Polynomial.C (10 : K) * E * H.derivative -
              H * E.derivative) := by ring
      _ = 0 := by
        rw [hC10]
        have hfac :
            (10 : K[X]) * E * H.derivative - H * E.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 10 hH) hW

/-! ## Square chamber -/

/-- Cleared square-core form of the fourth defect relation: cancelling
`h₀¹²` from `E = κ₃ h₀²⁰` on `p₅ = h₀³ w`, `D = μ h₀¹⁵` leaves the
degree-`8` chamber core with the `h₀`-free quartic
`270 p₄² - 90 p₄ w² + 10 w⁴`. -/
theorem alignedSquareFourth_core_610 {K : Type*} [Field K] [CharZero K]
    {H h0 w a2 a3 a4 a5 b6 b7 : K[X]} {κ μ κ₃ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp5 : a5 = h0 ^ 3 * w)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10) :
    (810 : K[X]) * a2 * h0 ^ 6 - (486 : K[X]) * b6 * h0 ^ 2 +
        (540 : K[X]) * a3 * w * h0 ^ 3 + (270 : K[X]) * a4 ^ 2 -
        (90 : K[X]) * a4 * w ^ 2 + (10 : K[X]) * w ^ 4 +
        Polynomial.C κ *
          ((72 : K[X]) * a4 * h0 ^ 4 + (12 : K[X]) * w ^ 2 * h0 ^ 4) -
        Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 6) =
      Polynomial.C κ₃ * h0 ^ 8 := by
  have hE' := hE
  simp only [alignedFourthDefect610] at hE'
  rw [hD, hHsq, hp5] at hE'
  apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
  linear_combination hE'

/-- The consumed degree-`11` row in the square chamber: the quartic tie
`270 p₄² - 90 p₄ w² + 10 w⁴ = h₀² r` — the first constraint on `p₄` in
the aligned tower — and the sextic row solved against the new quotient
`r`. -/
theorem alignedSquareFourth_tie_610 {K : Type*} [Field K] [CharZero K]
    {h0 w a2 a3 a4 b6 : K[X]} {κ μ κ₃ : K}
    (hcore :
      (810 : K[X]) * a2 * h0 ^ 6 - (486 : K[X]) * b6 * h0 ^ 2 +
          (540 : K[X]) * a3 * w * h0 ^ 3 + (270 : K[X]) * a4 ^ 2 -
          (90 : K[X]) * a4 * w ^ 2 + (10 : K[X]) * w ^ 4 +
          Polynomial.C κ *
            ((72 : K[X]) * a4 * h0 ^ 4 + (12 : K[X]) * w ^ 2 * h0 ^ 4) -
          Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 6) =
        Polynomial.C κ₃ * h0 ^ 8) :
    ∃ r : K[X],
      (270 : K[X]) * a4 ^ 2 - (90 : K[X]) * a4 * w ^ 2 +
          (10 : K[X]) * w ^ 4 = h0 ^ 2 * r ∧
        (486 : K[X]) * b6 =
          (810 : K[X]) * a2 * h0 ^ 4 + (540 : K[X]) * a3 * w * h0 + r +
            Polynomial.C κ *
              ((72 : K[X]) * a4 * h0 ^ 2 + (12 : K[X]) * w ^ 2 * h0 ^ 2) -
            Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 4) -
            Polynomial.C κ₃ * h0 ^ 6 := by
  refine ⟨(486 : K[X]) * b6 - (810 : K[X]) * a2 * h0 ^ 4 -
      (540 : K[X]) * a3 * w * h0 -
      Polynomial.C κ *
        ((72 : K[X]) * a4 * h0 ^ 2 + (12 : K[X]) * w ^ 2 * h0 ^ 2) +
      Polynomial.C μ * ((7 : K[X]) * w * h0 ^ 4) +
      Polynomial.C κ₃ * h0 ^ 6, ?_, ?_⟩
  · linear_combination hcore
  · ring

/-- At the root of the square core the quartic tie evaluates to the
normalized relation `27 p₄(a)² - 9 p₄(a) w(a)² + w(a)⁴ = 0`. -/
theorem alignedSquareFourth_rootTie_610 {K : Type*} [Field K] [CharZero K]
    {h0 w a4 r : K[X]}
    (htie : (270 : K[X]) * a4 ^ 2 - (90 : K[X]) * a4 * w ^ 2 +
        (10 : K[X]) * w ^ 4 = h0 ^ 2 * r)
    {a : K} (ha : h0.eval a = 0) :
    27 * a4.eval a ^ 2 - 9 * a4.eval a * w.eval a ^ 2 +
        w.eval a ^ 4 = 0 := by
  have hev := congrArg (fun t : K[X] => t.eval a) htie
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
  rw [ha] at hev
  linear_combination (10⁻¹ : K) * hev

/-! ## Nonsquare chamber -/

/-- Cleared nonsquare-core form of the fourth defect relation:
cancelling `H⁶` from `E = κ₃ H¹⁰` on `p₅ = H² g₁`, `D = 0` leaves the
degree-`4` chamber core whose `H`-free part is `270 p₄²`. -/
theorem alignedNonsquareFourth_core_610 {K : Type*} [Field K] [CharZero K]
    {H g1 a2 a3 a4 a5 b6 b7 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hg1 : a5 = H ^ 2 * g1)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10) :
    (810 : K[X]) * a2 * H ^ 3 - (486 : K[X]) * b6 * H +
        (540 : K[X]) * a3 * g1 * H ^ 2 + (270 : K[X]) * a4 ^ 2 -
        (90 : K[X]) * a4 * g1 ^ 2 * H + (10 : K[X]) * g1 ^ 4 * H ^ 2 +
        Polynomial.C κ *
          ((72 : K[X]) * a4 * H ^ 2 + (12 : K[X]) * g1 ^ 2 * H ^ 3) =
      Polynomial.C κ₃ * H ^ 4 := by
  have hE' := hE
  simp only [alignedFourthDefect610] at hE'
  rw [hD0, hg1] at hE'
  apply mul_left_cancel₀ (pow_ne_zero 6 hH)
  linear_combination hE'

/-- In the nonsquare chamber every root of the core kills `p₄`, so the
full quadratic core divides it: the first constraint on `p₄` in the
aligned tower. -/
theorem alignedNonsquareFourth_dvd_p4_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 a2 a3 a4 b6 : k[X]} {κ κ₃ : k}
    (hdeg : H.natDegree = 2) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hcore :
      (810 : k[X]) * a2 * H ^ 3 - (486 : k[X]) * b6 * H +
          (540 : k[X]) * a3 * g1 * H ^ 2 + (270 : k[X]) * a4 ^ 2 -
          (90 : k[X]) * a4 * g1 ^ 2 * H + (10 : k[X]) * g1 ^ 4 * H ^ 2 +
          Polynomial.C κ *
            ((72 : k[X]) * a4 * H ^ 2 + (12 : k[X]) * g1 ^ 2 * H ^ 3) =
        Polynomial.C κ₃ * H ^ 4) :
    H ∣ a4 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hq : (270 : k[X]) * a4 ^ 2 =
      H * (Polynomial.C κ₃ * H ^ 3 - (810 : k[X]) * a2 * H ^ 2 +
        (486 : k[X]) * b6 - (540 : k[X]) * a3 * g1 * H +
        (90 : k[X]) * a4 * g1 ^ 2 - (10 : k[X]) * g1 ^ 4 * H -
        Polynomial.C κ *
          ((72 : k[X]) * a4 * H + (12 : k[X]) * g1 ^ 2 * H ^ 2)) := by
    linear_combination hcore
  have hroot : ∀ a : k, H.eval a = 0 → a4.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun t : k[X] => t.eval a) hq
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [ha, zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (270 : k) ≠ 0))
  exact dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hroot

/-- Simple-root form of the consumed degree-`11` row in the nonsquare
chamber: with `p₄ = H f` the sextic coefficient is solved with an
explicit `H` factor. -/
theorem alignedNonsquareFourth_solved_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f a2 a3 a4 b6 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hf : a4 = H * f)
    (hcore :
      (810 : K[X]) * a2 * H ^ 3 - (486 : K[X]) * b6 * H +
          (540 : K[X]) * a3 * g1 * H ^ 2 + (270 : K[X]) * a4 ^ 2 -
          (90 : K[X]) * a4 * g1 ^ 2 * H + (10 : K[X]) * g1 ^ 4 * H ^ 2 +
          Polynomial.C κ *
            ((72 : K[X]) * a4 * H ^ 2 + (12 : K[X]) * g1 ^ 2 * H ^ 3) =
        Polynomial.C κ₃ * H ^ 4) :
    (486 : K[X]) * b6 =
      H * ((810 : K[X]) * a2 * H + (540 : K[X]) * a3 * g1 +
        (270 : K[X]) * f ^ 2 - (90 : K[X]) * f * g1 ^ 2 +
        (10 : K[X]) * g1 ^ 4 +
        Polynomial.C κ * ((72 : K[X]) * f * H + (12 : K[X]) * g1 ^ 2 * H) -
        Polynomial.C κ₃ * H ^ 2) := by
  have hcore' := hcore
  rw [hf] at hcore'
  have h2 : H * (H * ((810 : K[X]) * a2 * H + (540 : K[X]) * a3 * g1 +
      (270 : K[X]) * f ^ 2 - (90 : K[X]) * f * g1 ^ 2 +
      (10 : K[X]) * g1 ^ 4 +
      Polynomial.C κ * ((72 : K[X]) * f * H + (12 : K[X]) * g1 ^ 2 * H) -
      Polynomial.C κ₃ * H ^ 2) - (486 : K[X]) * b6) = 0 := by
    linear_combination hcore'
  have h3 := (mul_eq_zero.mp h2).resolve_left hH
  linear_combination -h3

/-! ## Source-facing fourth-row packets -/

/-- Source-facing weight-ten integral of a normalized aligned scale-two
`(6,10)` source: the degree-`11` row is consumed into `E = κ₃ H¹⁰` on
top of the previous aligned packet, chamber-free. -/
theorem normalized610ScaleTwo_alignedFourthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ : K),
      q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₂ * H ^ 15 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 := by
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
  exact ⟨κ, κ₂, κ₃, aligned_q9_solved_610 haligned, hM, hD2, hE⟩

/-- Exact square-chamber fourth packet of a normalized aligned scale-two
`(6,10)` source: the previous packet plus the quartic tie
`270 p₄² - 90 p₄ w² + 10 w⁴ = h₀² r` and the solved sextic row
`486 q₆ = 810 p₂ h₀⁴ + 540 p₃ w h₀ + r + κ (72 p₄ h₀² + 12 w² h₀²)
- 7 μ w h₀⁴ - κ₃ h₀⁶`. -/
theorem normalized610ScaleTwo_alignedFourthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ : K) (w r : K[X]),
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
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 := by
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
  have hcore := alignedSquareFourth_core_610 hh0 hHsq hp5 hD hE4
  obtain ⟨r, htie, hq6⟩ := alignedSquareFourth_tie_610 hcore
  refine ⟨κ, μ, κ₃, w, r, hp5, ?_, ?_, hq7, htie, hq6, hE4⟩
  · rw [hq9, hg, hgw, hHsq]; ring
  · rw [hq8, hgw]; ring

/-- Exact nonsquare-chamber fourth packet of a normalized aligned
scale-two `(6,10)` source: the previous packet plus the new
divisibility `p₄ = H f` and the solved sextic row
`486 q₆ = H (810 p₂ H + 540 p₃ g₁ + 270 f² - 90 f g₁² + 10 g₁⁴
+ κ (72 f H + 12 g₁² H) - κ₃ H²)`; in particular `H ∣ p₄` and
`H ∣ q₆`. -/
theorem normalized610ScaleTwo_alignedFourthFace_nonsquareChamber_packet
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
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect610 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 10 := by
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
  have hcore := alignedNonsquareFourth_core_610 hH hp5 hD0 hE4
  obtain ⟨f, hf⟩ := alignedNonsquareFourth_dvd_p4_610 hHdegree hnsq hcore
  have hq6 := alignedNonsquareFourth_solved_610 hH hf hcore
  refine ⟨κ, κ₃, g1, f, hp5, ?_, ?_, hq7, hf, hq6, hD0, hE4⟩
  · rw [hq9, hg, hg1]; ring
  · rw [hq8, hg1]; ring

/-- Honest square/nonsquare chamber split of the consumed degree-`11`
aligned row.  Neither chamber is excluded and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedFourthFace_chamberDichotomy
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
      ∃ (κ μ κ₃ : K) (w r : K[X]),
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
              Polynomial.C κ₃ * h0 ^ 6) ∨
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
              Polynomial.C κ₃ * H ^ 2)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedFourthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, w, r, hp5, hq9, hq8, hq7, htie, hq6, _hE⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₃, w, r, hp5, hq9, hq8, hq7,
      htie, hq6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedFourthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6, _hD0, _hE⟩ :=
      hpacket
    exact Or.inr ⟨hnsq, κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6⟩

/-- Root data of the consumed degree-`11` row: at scale two the common
core has a root where the previous jet `p₅, q₉, q₈, q₇` vanishes, and
the new row adds the honest chamber-dependent gain — the quartic tie
`27 p₄(a)² - 9 p₄(a) w(a)² + w(a)⁴ = 0` in the square chamber, and
`p₄(a) = 0` with `q₆(a) = 0` in the nonsquare chamber. -/
theorem normalized610ScaleTwo_alignedFourthFace_rootData
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
      ((∃ h0 w : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 3 * w ∧
          27 * (p.coeff 4).eval a ^ 2 -
              9 * (p.coeff 4).eval a * w.eval a ^ 2 +
              w.eval a ^ 4 = 0) ∨
        ((p.coeff 4).eval a = 0 ∧ (q.coeff 6).eval a = 0)) := by
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
      normalized610ScaleTwo_alignedFourthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, w, r, hp5, hq9, hq8, hq7, htie, hq6, _hE⟩ := hpacket
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    refine ⟨a, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w, hh0, hHsq, hroot, hp5,
        alignedSquareFourth_rootTie_610 htie hroot⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul]
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
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedFourthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g1, f, hp5, hq9, hq8, hq7, hf, hq6, _hD0, _hE⟩ :=
      hpacket
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
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

#print axioms alignedFourthCoefficientJacobianRow_610
#print axioms alignedFourthDefect_weightedDerivative_identity_610
#print axioms alignedFourthDefectRow_eq_zero_610
#print axioms alignedFourthDefectPowerRelation_610
#print axioms alignedSquareFourth_core_610
#print axioms alignedSquareFourth_tie_610
#print axioms alignedSquareFourth_rootTie_610
#print axioms alignedNonsquareFourth_core_610
#print axioms alignedNonsquareFourth_dvd_p4_610
#print axioms alignedNonsquareFourth_solved_610
#print axioms normalized610ScaleTwo_alignedFourthFace_packet
#print axioms normalized610ScaleTwo_alignedFourthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedFourthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedFourthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedFourthFace_rootData

end Max11DegreeRoutes
