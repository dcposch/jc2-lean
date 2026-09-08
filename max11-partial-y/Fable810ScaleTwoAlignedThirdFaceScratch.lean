import Fable810ScaleTwoAlignedSecondFaceScratch

/-! # Third aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedSecondFaceScratch` consumed the degree-`14`
aligned Keller row of the normalized scale-two `(8,10)` source: the
squared weight-twenty-one integral `D² = κ₂ H²¹` of the half-weight
defect `D`, the chamber descents `p₇ = h₀⁴ g₁` / `p₇ = H² g₂`, the
factored quotient rows, and the honest root branch
`g = 0 ∨ g² = 8 p₆`.  This file consumes the next unused aligned row,
the degree-`13` Jacobian coefficient — the first row that sees `p₄` and
`q₆`.

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`, the
consumed degree-`15` relation
`C = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇² - κ H⁷ = 0`, and the consumed
degree-`14` row `2 H D' - 21 D H' = 0`, the degree-`13` row is the
weighted derivative of the weight-twenty-eight defect

`E = 2560 p₄ H¹² - 2048 q₆ H¹¹ - 1600 p₅ p₇ H⁸ + 1792 p₇ q₇ H⁷
  - 800 p₆ p₇² H⁴ + 320 p₆² H⁸ + 105 p₇⁴ + κ (64 p₆ H¹¹ - 56 p₇² H⁷)`,

via the exact multiplier identity

`256 H⁸ · row₁₃[p₈ = H⁴, q₁₀ = H⁵] = (H E' - 14 E H')
  - 576 H⁸ p₅' N + 320 H⁸ p₅ N' + (64 H⁵ p₆' + 144 p₆ H⁴ H') C
  - 48 H⁵ p₆ C' + 14 p₇ (2 H D' - 21 D H')`.

On the aligned face every right-hand correction vanishes, so
`H E' = 14 E H'` and the weight-twenty-eight polynomial first integral

`E = κ₃ H¹⁴`

holds for a preserved constant `κ₃`.  Unlike the two previous aligned
rows the exponent is even, so the integral is chamber-free: no new
square/nonsquare forcing occurs, and `κ₃` is preserved in both chambers.
The chamber split enters only through the previous packet:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`, `D = μ h₀²¹`: peeling `h₀¹⁶`
  and consuming the previous factored quotient (`128 q₇ h₀²` solved)
  leaves the cleared fourth row
  `2560 p₄ h₀⁸ - 2048 q₆ h₀⁶ + 640 p₅ g₁ h₀⁴ + 320 p₆² - 240 p₆ g₁²
   + 35 g₁⁴ + 64 κ p₆ h₀⁶ - 14 μ g₁ h₀⁹ = κ₃ h₀¹²`.
* nonsquare chamber, `p₇ = H² g₂`, `D = 0`: peeling `H⁸` and consuming
  the previous factored quotient (`128 q₇ H` solved) leaves
  `2560 p₄ H⁴ - 2048 q₆ H³ + 640 p₅ g₂ H² + 320 p₆² - 240 p₆ g₂²
   + 35 g₂⁴ + 64 κ p₆ H³ = κ₃ H⁶`.

In both chambers the cleared row evaluates at every root of the core to
the same quartic `320 p₆² - 240 p₆ g² + 35 g⁴ = 0`.  Combined with the
previous honest root branch `g = 0 ∨ g² = 8 p₆` this collapses: on
`g = 0` the quartic forces `320 p₆² = 0`, and on `g² = 8 p₆` it forces
`640 p₆² = 0`; either way `p₆ = 0` and then `g = 0` at the root.  The
quadratic branch is therefore eliminated *at the root* (not as a
polynomial identity), and the descent deepens by one step in each
chamber: `h₀ ∣ g₁` and `h₀ ∣ p₆` in the square chamber, `H ∣ g₂` and
`H ∣ p₆` in the nonsquare chamber.  The chamber-independent root jet
extends to `p₆`: at a root of the common core the coefficients
`p₇, q₉, q₈, p₆` all vanish.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`linearPolynomial_dvd_of_eval_eq_zero_810` (all generic in the degree
pair).  No closure is claimed.  Both chambers remain open, the constants
`κ`, `μ`, `κ₃` are preserved and not cleared, the zero branches
(`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`) are not excluded as
polynomial identities, the deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`,
`p₆/H` are not re-cleared through the tower here, and no individual
vanishing of `p₄`, `p₅`, `q₆`, `q₇` is claimed.  The next unused Keller
row on the aligned face is the degree-`12` Jacobian coefficient, the
first row that sees `p₃` and `q₅`.  No total-degree or twice-prime
theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`13` Keller coefficient on the aligned face -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`13` Jacobian coefficient, the first
aligned row that sees `p₄` and `q₆`. -/
theorem alignedFourthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 7).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 6).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 5).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 4).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 6).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 7).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 8).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 9).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) *
          (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 13) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (13 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
      ({(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
        (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1),
        (13, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC6, hC7, hC8, hC9, hC10, hC5, hC4]
  linear_combination hcoeff

/-! ## Aligned fourth defect -/

/-- Weight-twenty-eight defect of the degree-`13` aligned `(8,10)` row:
`E = 2560 p₄ H¹² - 2048 q₆ H¹¹ - 1600 p₅ p₇ H⁸ + 1792 p₇ q₇ H⁷
 - 800 p₆ p₇² H⁴ + 320 p₆² H⁸ + 105 p₇⁴ + κ (64 p₆ H¹¹ - 56 p₇² H⁷)`.
On the aligned face it is an actual polynomial first integral with even
exponent — no square root of `H` and no chamber split are required. -/
def alignedFourthDefect810 {K : Type*} [CommRing K]
    (H a4 a5 a6 a7 b6 b7 : K[X]) (κ : K) : K[X] :=
  (2560 : K[X]) * a4 * H ^ 12 - (2048 : K[X]) * b6 * H ^ 11 -
    (1600 : K[X]) * a5 * a7 * H ^ 8 + (1792 : K[X]) * a7 * b7 * H ^ 7 -
    (800 : K[X]) * a6 * a7 ^ 2 * H ^ 4 + (320 : K[X]) * a6 ^ 2 * H ^ 8 +
    (105 : K[X]) * a7 ^ 4 +
    Polynomial.C κ *
      ((64 : K[X]) * a6 * H ^ 11 - (56 : K[X]) * a7 ^ 2 * H ^ 7)

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`13` Jacobian expression with the
weighted derivative of `E`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` and
degree-`14` rows. -/
theorem alignedFourthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K] (H a4 a5 a6 a7 b6 b7 b8 b9 : K[X]) (κ : K) :
    (256 : K[X]) * H ^ 8 *
        ((H ^ 4).derivative * (b6 * (6 : K[X])) +
          a7.derivative * (b7 * (7 : K[X])) +
          a6.derivative * (b8 * (8 : K[X])) +
          a5.derivative * (b9 * (9 : K[X])) +
          a4.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b6.derivative +
          (a7 * (7 : K[X])) * b7.derivative +
          (a6 * (6 : K[X])) * b8.derivative +
          (a5 * (5 : K[X])) * b9.derivative +
          (a4 * (4 : K[X])) * (H ^ 5).derivative)) =
      (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
        (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
          H.derivative) -
        (576 : K[X]) * H ^ 8 * a5.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (320 : K[X]) * H ^ 8 * a5 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((64 : K[X]) * H ^ 5 * a6.derivative +
            (144 : K[X]) * a6 * H ^ 4 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (48 : K[X]) * H ^ 5 * a6 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        (14 : K[X]) * a7 *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) := by
  simp only [alignedFourthDefect810, alignedThirdDefect810,
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

/-- On the aligned face, with the consumed degree-`15` and degree-`14`
rows, the degree-`13` row is the weighted derivative
`H E' - 14 E H' = 0`. -/
theorem alignedFourthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H * (alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
          (p.coeff 7) (q.coeff 6) (q.coeff 7) κ).derivative -
      (14 : K[X]) *
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
          (p.coeff 7) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedFourthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  rw [hC6, hC7, hC8, hC9, hC10, hC5, hC4] at hrow
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
  have hid := alignedFourthDefect_weightedDerivative_identity_810
    H (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 6)
    (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-twenty-eight polynomial first integral of the aligned
`(8,10)` fourth defect: `E = κ₃ H¹⁴`.  The exponent is even, so the
integral is chamber-free. -/
theorem alignedFourthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₃ : K,
      alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
          (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₃ * H ^ 14 := by
  let E : K[X] :=
    alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
      (p.coeff 7) (q.coeff 6) (q.coeff 7) κ
  have hrow : H * E.derivative - (14 : K[X]) * E * H.derivative = 0 := by
    simpa only [E] using
      alignedFourthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC14 : Polynomial.C (14 : K) = (14 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian E (H ^ 14) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      E * (Polynomial.C (14 : K) * H ^ (14 - 1) * H.derivative) -
          E.derivative * H ^ 14 =
          H ^ 13 *
            (Polynomial.C (14 : K) * E * H.derivative -
              H * E.derivative) := by ring
      _ = 0 := by
        rw [hC14]
        have hfac :
            (14 : K[X]) * E * H.derivative - H * E.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 14 hH) hW

/-! ## Root quartic and branch collapse -/

/-- At a root of the core the cleared fourth row leaves the quartic
`320 p₆² - 240 p₆ g² + 35 g⁴ = 0`; combined with the previous honest
root branch `g = 0 ∨ g² = 8 p₆` it collapses both branches:
`p₆` and the descent quotient `g` both vanish at the root. -/
theorem alignedFourth_rootCollapse_810 {K : Type*} [Field K] [CharZero K]
    {P6 G : K}
    (hquartic : 320 * P6 ^ 2 - 240 * P6 * G ^ 2 + 35 * G ^ 4 = 0)
    (hbranch : G = 0 ∨ G ^ 2 = 8 * P6) :
    G = 0 ∧ P6 = 0 := by
  rcases hbranch with hG | hG2
  · refine ⟨hG, ?_⟩
    rw [hG] at hquartic
    have h320 : (320 : K) * P6 ^ 2 = 0 := by linear_combination hquartic
    have hsq : P6 ^ 2 = 0 :=
      (mul_eq_zero.mp h320).resolve_left (by norm_num : (320 : K) ≠ 0)
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
  · have h640 : (640 : K) * P6 ^ 2 = 0 := by
      linear_combination hquartic - (35 * G ^ 2 + 40 * P6) * hG2
    have hP6 : P6 = 0 := by
      have hsq : P6 ^ 2 = 0 :=
        (mul_eq_zero.mp h640).resolve_left (by norm_num : (640 : K) ≠ 0)
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
    have hG : G = 0 := by
      have hsq : G ^ 2 = 0 := by rw [hG2, hP6, mul_zero]
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
    exact ⟨hG, hP6⟩

/-! ## Square chamber -/

/-- Peeling `h₀¹⁶` from `E = κ₃ h₀²⁸` on `p₇ = h₀⁴ g₁` leaves the
square-chamber fourth core. -/
theorem alignedSquareFourth_core_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a4 a5 a6 a7 b6 b7 : K[X]} {κ κ₃ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hE : alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 14) :
    (2560 : K[X]) * a4 * h0 ^ 8 - (2048 : K[X]) * b6 * h0 ^ 6 -
        (1600 : K[X]) * a5 * g1 * h0 ^ 4 +
        (1792 : K[X]) * g1 * b7 * h0 ^ 2 -
        (800 : K[X]) * a6 * g1 ^ 2 + (320 : K[X]) * a6 ^ 2 +
        (105 : K[X]) * g1 ^ 4 +
        Polynomial.C κ *
          ((64 : K[X]) * a6 * h0 ^ 6 - (56 : K[X]) * g1 ^ 2 * h0 ^ 6) =
      Polynomial.C κ₃ * h0 ^ 12 := by
  have hE' :
      (2560 : K[X]) * a4 * (h0 ^ 2) ^ 12 -
          (2048 : K[X]) * b6 * (h0 ^ 2) ^ 11 -
          (1600 : K[X]) * a5 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 8 +
          (1792 : K[X]) * (h0 ^ 4 * g1) * b7 * (h0 ^ 2) ^ 7 -
          (800 : K[X]) * a6 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 4 +
          (320 : K[X]) * a6 ^ 2 * (h0 ^ 2) ^ 8 +
          (105 : K[X]) * (h0 ^ 4 * g1) ^ 4 +
          Polynomial.C κ *
            ((64 : K[X]) * a6 * (h0 ^ 2) ^ 11 -
              (56 : K[X]) * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 7) =
        Polynomial.C κ₃ * (h0 ^ 2) ^ 14 := by
    simpa only [alignedFourthDefect810, hHsq, hg] using hE
  apply mul_left_cancel₀ (pow_ne_zero 16 hh0)
  linear_combination hE'

/-- Consuming the previous factored quotient (`128 q₇ h₀²` solved)
eliminates `q₇` from the square-chamber fourth core: the cleared fourth
row of the square chamber, with the root quartic visible at `h₀ = 0`. -/
theorem alignedSquareFourth_solved_810 {K : Type*} [Field K] [CharZero K]
    {h0 g1 a4 a5 a6 b6 b7 : K[X]} {κ κ₃ μ : K}
    (hcore :
      (2560 : K[X]) * a4 * h0 ^ 8 - (2048 : K[X]) * b6 * h0 ^ 6 -
          (1600 : K[X]) * a5 * g1 * h0 ^ 4 +
          (1792 : K[X]) * g1 * b7 * h0 ^ 2 -
          (800 : K[X]) * a6 * g1 ^ 2 + (320 : K[X]) * a6 ^ 2 +
          (105 : K[X]) * g1 ^ 4 +
          Polynomial.C κ *
            ((64 : K[X]) * a6 * h0 ^ 6 -
              (56 : K[X]) * g1 ^ 2 * h0 ^ 6) =
        Polynomial.C κ₃ * h0 ^ 12)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    (2560 : K[X]) * a4 * h0 ^ 8 - (2048 : K[X]) * b6 * h0 ^ 6 +
        (640 : K[X]) * a5 * g1 * h0 ^ 4 + (320 : K[X]) * a6 ^ 2 -
        (240 : K[X]) * a6 * g1 ^ 2 + (35 : K[X]) * g1 ^ 4 +
        Polynomial.C κ * ((64 : K[X]) * a6 * h0 ^ 6) -
        Polynomial.C μ * ((14 : K[X]) * g1 * h0 ^ 9) =
      Polynomial.C κ₃ * h0 ^ 12 := by
  linear_combination hcore - (14 : K[X]) * g1 * hq7

/-! ## Nonsquare chamber -/

/-- Peeling `H⁸` from `E = κ₃ H¹⁴` on `p₇ = H² g₂` leaves the
nonsquare-chamber fourth core. -/
theorem alignedNonsquareFourth_core_810 {K : Type*} [Field K] [CharZero K]
    {H g2 a4 a5 a6 a7 b6 b7 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hE : alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 14) :
    (2560 : K[X]) * a4 * H ^ 4 - (2048 : K[X]) * b6 * H ^ 3 -
        (1600 : K[X]) * a5 * g2 * H ^ 2 + (1792 : K[X]) * g2 * b7 * H -
        (800 : K[X]) * a6 * g2 ^ 2 + (320 : K[X]) * a6 ^ 2 +
        (105 : K[X]) * g2 ^ 4 +
        Polynomial.C κ *
          ((64 : K[X]) * a6 * H ^ 3 - (56 : K[X]) * g2 ^ 2 * H ^ 3) =
      Polynomial.C κ₃ * H ^ 6 := by
  have hE' :
      (2560 : K[X]) * a4 * H ^ 12 - (2048 : K[X]) * b6 * H ^ 11 -
          (1600 : K[X]) * a5 * (H ^ 2 * g2) * H ^ 8 +
          (1792 : K[X]) * (H ^ 2 * g2) * b7 * H ^ 7 -
          (800 : K[X]) * a6 * (H ^ 2 * g2) ^ 2 * H ^ 4 +
          (320 : K[X]) * a6 ^ 2 * H ^ 8 +
          (105 : K[X]) * (H ^ 2 * g2) ^ 4 +
          Polynomial.C κ *
            ((64 : K[X]) * a6 * H ^ 11 -
              (56 : K[X]) * (H ^ 2 * g2) ^ 2 * H ^ 7) =
        Polynomial.C κ₃ * H ^ 14 := by
    simpa only [alignedFourthDefect810, hg2] using hE
  apply mul_left_cancel₀ (pow_ne_zero 8 hH)
  linear_combination hE'

/-- Consuming the previous factored quotient (`128 q₇ H` solved)
eliminates `q₇` from the nonsquare-chamber fourth core: the cleared
fourth row of the nonsquare chamber. -/
theorem alignedNonsquareFourth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a4 a5 a6 b6 b7 : K[X]} {κ κ₃ : K}
    (hcore :
      (2560 : K[X]) * a4 * H ^ 4 - (2048 : K[X]) * b6 * H ^ 3 -
          (1600 : K[X]) * a5 * g2 * H ^ 2 +
          (1792 : K[X]) * g2 * b7 * H -
          (800 : K[X]) * a6 * g2 ^ 2 + (320 : K[X]) * a6 ^ 2 +
          (105 : K[X]) * g2 ^ 4 +
          Polynomial.C κ *
            ((64 : K[X]) * a6 * H ^ 3 -
              (56 : K[X]) * g2 ^ 2 * H ^ 3) =
        Polynomial.C κ₃ * H ^ 6)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    (2560 : K[X]) * a4 * H ^ 4 - (2048 : K[X]) * b6 * H ^ 3 +
        (640 : K[X]) * a5 * g2 * H ^ 2 + (320 : K[X]) * a6 ^ 2 -
        (240 : K[X]) * a6 * g2 ^ 2 + (35 : K[X]) * g2 ^ 4 +
        Polynomial.C κ * ((64 : K[X]) * a6 * H ^ 3) =
      Polynomial.C κ₃ * H ^ 6 := by
  linear_combination hcore - (14 : K[X]) * g2 * hfac

/-! ## Root evaluation of the cleared fourth rows -/

/-- The square-chamber cleared fourth row leaves exactly the collapse
quartic at the root of the linear core. -/
theorem alignedSquareFourth_rootQuartic_810 {K : Type*}
    [Field K] [CharZero K]
    {h0 g1 a4 a5 a6 b6 : K[X]} {κ κ₃ μ : K}
    (hsolved :
      (2560 : K[X]) * a4 * h0 ^ 8 - (2048 : K[X]) * b6 * h0 ^ 6 +
          (640 : K[X]) * a5 * g1 * h0 ^ 4 + (320 : K[X]) * a6 ^ 2 -
          (240 : K[X]) * a6 * g1 ^ 2 + (35 : K[X]) * g1 ^ 4 +
          Polynomial.C κ * ((64 : K[X]) * a6 * h0 ^ 6) -
          Polynomial.C μ * ((14 : K[X]) * g1 * h0 ^ 9) =
        Polynomial.C κ₃ * h0 ^ 12)
    {a : K} (ha : h0.eval a = 0) :
    320 * (a6.eval a) ^ 2 - 240 * a6.eval a * (g1.eval a) ^ 2 +
      35 * (g1.eval a) ^ 4 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hsolved
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hev
  rw [ha] at hev
  linear_combination hev

/-- The nonsquare-chamber cleared fourth row leaves the same collapse
quartic at every root of the core. -/
theorem alignedNonsquareFourth_rootQuartic_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a4 a5 a6 b6 : K[X]} {κ κ₃ : K}
    (hsolved :
      (2560 : K[X]) * a4 * H ^ 4 - (2048 : K[X]) * b6 * H ^ 3 +
          (640 : K[X]) * a5 * g2 * H ^ 2 + (320 : K[X]) * a6 ^ 2 -
          (240 : K[X]) * a6 * g2 ^ 2 + (35 : K[X]) * g2 ^ 4 +
          Polynomial.C κ * ((64 : K[X]) * a6 * H ^ 3) =
        Polynomial.C κ₃ * H ^ 6)
    {a : K} (ha : H.eval a = 0) :
    320 * (a6.eval a) ^ 2 - 240 * a6.eval a * (g2.eval a) ^ 2 +
      35 * (g2.eval a) ^ 4 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hsolved
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_ofNat] at hev
  rw [ha] at hev
  linear_combination hev

/-! ## Source-facing fourth-row packets -/

/-- Source-facing weight-twenty-eight integral of a normalized aligned
scale-two `(8,10)` source: the degree-`13` row is consumed into the
chamber-free polynomial first integral `E = κ₃ H¹⁴` on top of the
previous aligned packet. -/
theorem normalized810ScaleTwo_alignedFourthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 := by
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
  exact ⟨κ, κ₃, aligned_q9_solved_810 haligned, hM, hE4⟩

/-- Exact square-chamber fourth packet of a normalized aligned scale-two
`(8,10)` source: on top of `p₇ = h₀⁴ g₁`, `q₉ = (5/4) g₁ h₀⁶`, and the
solved `q₈`, the consumed degree-`13` row gives the cleared fourth row
`2560 p₄ h₀⁸ - 2048 q₆ h₀⁶ + 640 p₅ g₁ h₀⁴ + 320 p₆² - 240 p₆ g₁²
 + 35 g₁⁴ + 64 κ p₆ h₀⁶ - 14 μ g₁ h₀⁹ = κ₃ h₀¹²`, the root collapse
`g₁ = p₆ = 0` at the root of the linear core (the quadratic branch
`g₁² = 8 p₆` is eliminated there), the deepened descents `h₀ ∣ g₁` and
`h₀ ∣ p₆`, and the chamber-free integral `E = κ₃ H¹⁴`. -/
theorem normalized810ScaleTwo_alignedFourthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        (32 : K[X]) * q.coeff 8 =
          h0 ^ 2 * ((5 : K[X]) * g1 ^ 2 + (40 : K[X]) * p.coeff 6 +
            Polynomial.C κ * h0 ^ 6) ∧
        (2560 : K[X]) * p.coeff 4 * h0 ^ 8 -
            (2048 : K[X]) * q.coeff 6 * h0 ^ 6 +
            (640 : K[X]) * p.coeff 5 * g1 * h0 ^ 4 +
            (320 : K[X]) * p.coeff 6 ^ 2 -
            (240 : K[X]) * p.coeff 6 * g1 ^ 2 +
            (35 : K[X]) * g1 ^ 4 +
            Polynomial.C κ * ((64 : K[X]) * p.coeff 6 * h0 ^ 6) -
            Polynomial.C μ * ((14 : K[X]) * g1 * h0 ^ 9) =
          Polynomial.C κ₃ * h0 ^ 12 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 := by
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
  have hq8 := alignedSquare_q8_solved_810 hh0 hHsq hg hM
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
  have hsolved := alignedSquareFourth_solved_810 hcore4 hcore
  have hcollapse : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedSquareFourth_rootQuartic_810 hsolved ha) (hbranch a ha)
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
  exact ⟨κ, μ, κ₃, g1, hp7, by rw [hq9, hg, hg1, hHsq]; ring,
    by rw [hq8, hg1]; ring, hsolved, hcollapse, hdvdg1, hdvdp6, hE4⟩

/-- Exact nonsquare-chamber fourth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂`, `q₉ = (5/4) g₂ H³`,
and the solved `q₈`, the consumed degree-`13` row gives the cleared
fourth row
`2560 p₄ H⁴ - 2048 q₆ H³ + 640 p₅ g₂ H² + 320 p₆² - 240 p₆ g₂² + 35 g₂⁴
 + 64 κ p₆ H³ = κ₃ H⁶`, the root collapse `g₂ = p₆ = 0` at every
(simple) root of the core, the deepened descents `H ∣ g₂` and `H ∣ p₆`,
and the chamber-free integral `E = κ₃ H¹⁴`. -/
theorem normalized810ScaleTwo_alignedFourthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        (32 : K[X]) * q.coeff 8 =
          H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * p.coeff 6 +
            Polynomial.C κ * H ^ 3) ∧
        (2560 : K[X]) * p.coeff 4 * H ^ 4 -
            (2048 : K[X]) * q.coeff 6 * H ^ 3 +
            (640 : K[X]) * p.coeff 5 * g2 * H ^ 2 +
            (320 : K[X]) * p.coeff 6 ^ 2 -
            (240 : K[X]) * p.coeff 6 * g2 ^ 2 +
            (35 : K[X]) * g2 ^ 4 +
            Polynomial.C κ * ((64 : K[X]) * p.coeff 6 * H ^ 3) =
          Polynomial.C κ₃ * H ^ 6 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 := by
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
  have hq8 := alignedNonsquare_q8_solved_810 hH hg2 hM
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
  have hsolved := alignedNonsquareFourth_solved_810 hcore4 hfac
  have hcollapse : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedNonsquareFourth_rootQuartic_810 hsolved ha) (hbranch a ha)
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero
      hHdegree hnsq ha
  have hdvdg2 : H ∣ g2 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).1)
  have hdvdp6 : H ∣ p.coeff 6 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).2)
  exact ⟨κ, κ₃, g2, hg2, by rw [hq9, hg2]; ring, hq8, hsolved,
    hcollapse, hdvdg2, hdvdp6, hE4⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`13`
aligned row.  Neither chamber is excluded, the constants `κ`, `μ`, `κ₃`
are preserved and not cleared, and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedFourthFace_chamberDichotomy
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
      ∃ (κ μ κ₃ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (2560 : K[X]) * p.coeff 4 * h0 ^ 8 -
              (2048 : K[X]) * q.coeff 6 * h0 ^ 6 +
              (640 : K[X]) * p.coeff 5 * g1 * h0 ^ 4 +
              (320 : K[X]) * p.coeff 6 ^ 2 -
              (240 : K[X]) * p.coeff 6 * g1 ^ 2 +
              (35 : K[X]) * g1 ^ 4 +
              Polynomial.C κ * ((64 : K[X]) * p.coeff 6 * h0 ^ 6) -
              Polynomial.C μ * ((14 : K[X]) * g1 * h0 ^ 9) =
            Polynomial.C κ₃ * h0 ^ 12 ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₃ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (2560 : K[X]) * p.coeff 4 * H ^ 4 -
              (2048 : K[X]) * q.coeff 6 * H ^ 3 +
              (640 : K[X]) * p.coeff 5 * g2 * H ^ 2 +
              (320 : K[X]) * p.coeff 6 ^ 2 -
              (240 : K[X]) * p.coeff 6 * g2 ^ 2 +
              (35 : K[X]) * g2 ^ 4 +
              Polynomial.C κ * ((64 : K[X]) * p.coeff 6 * H ^ 3) =
            Polynomial.C κ₃ * H ^ 6 ∧
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
      normalized810ScaleTwo_alignedFourthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, g1, hp7, hq9, _hq8, hsolved, hcollapse,
      hdvdg1, hdvdp6, _hE4⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₃, g1, hp7, hq9, hsolved,
      hcollapse, hdvdg1, hdvdp6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedFourthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g2, hp7, hq9, _hq8, hsolved, hcollapse,
      hdvdg2, hdvdp6, _hE4⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₃, g2, hp7, hq9, hsolved,
      hcollapse, hdvdg2, hdvdp6⟩

/-- Extended chamber-independent root jet of the consumed degree-`13`
row: at scale two the common core has a root, and the jet
`p₇, q₉, q₈, p₆` vanishes there.  The sextic coefficients `p₄, q₆` are
*not* claimed to vanish — the consumed row ties them into the cleared
fourth row instead. -/
theorem normalized810ScaleTwo_alignedFourthFace_rootJet
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
      (p.coeff 6).eval a = 0 := by
  dsimp only at haligned ⊢
  have hjet := normalized810ScaleTwo_alignedThirdFace_rootJet
    hsource haligned
  dsimp only at hjet
  obtain ⟨a, hroot, hp7, hq9, hq8⟩ := hjet
  have hdi :=
    normalized810ScaleTwo_alignedFourthFace_chamberDichotomy
      hsource haligned
  dsimp only at hdi
  refine ⟨a, hroot, hp7, hq9, hq8, ?_⟩
  rcases hdi with
    ⟨h0, _hh0, hHsq, _κ, _μ, _κ₃, _g1, _hp7', _hq9', _hsolved,
      hcollapse, _hdvdg1, _hdvdp6⟩ |
    ⟨_hnsq, _κ, _κ₃, _g2, _hp7', _hq9', _hsolved, hcollapse,
      _hdvdg2, _hdvdp6⟩
  · have hh0root : h0.eval a = 0 := by
      have hev : H.eval a = (h0.eval a) ^ 2 := by
        rw [hHsq, Polynomial.eval_pow]
      rw [hroot] at hev
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev.symm
    exact (hcollapse a hh0root).2
  · exact (hcollapse a hroot).2

#print axioms alignedFourthCoefficientJacobianRow_810
#print axioms alignedFourthDefect_weightedDerivative_identity_810
#print axioms alignedFourthDefectRow_eq_zero_810
#print axioms alignedFourthDefectPowerRelation_810
#print axioms alignedFourth_rootCollapse_810
#print axioms alignedSquareFourth_core_810
#print axioms alignedSquareFourth_solved_810
#print axioms alignedNonsquareFourth_core_810
#print axioms alignedNonsquareFourth_solved_810
#print axioms alignedSquareFourth_rootQuartic_810
#print axioms alignedNonsquareFourth_rootQuartic_810
#print axioms normalized810ScaleTwo_alignedFourthFace_packet
#print axioms normalized810ScaleTwo_alignedFourthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedFourthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedFourthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedFourthFace_rootJet

end Max11DegreeRoutes
