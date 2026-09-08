import Fable410ScaleTwoAlignedSecondFaceScratch

/-! # Third aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedSecondFaceScratch` consumed the degree-`10`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`9/2` integral `M₂² = κ₂ H⁹` of the third defect
`M₂ = 5 p₃³ + 60 p₂ p₃ H² + 40 p₁ H⁴ + 4 κ p₃ H³ - 16 q₇ H`, with the
square chamber `M₂ = μ h₀⁹` and the nonsquare chamber `M₂ = 0`.  This
file consumes the next unused aligned row, the degree-`9` Jacobian
coefficient — the first row that sees `p₀` and `q₆` — derived here
directly from the literal Keller bracket.

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `C = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` row `2 H M₂' - 9 M₂ H' = 0`, the degree-`9`
row is the weighted derivative of the cleared fourth defect

`M₄ = 320 p₀ H⁶ - 128 q₆ H³ + 480 p₁ p₃ H⁴ + 240 p₂² H⁴
  + 120 p₂ p₃² H² - 5 p₃⁴ + κ (32 p₂ H⁵ + 16 p₃² H³) - 14 p₃ M₂`,

kept in factored form through the third defect `M₂`, via the exact
multiplier identity

`32 H² · row₉[p₄ = H², q₁₀ = H⁵] = (H M₄' - 6 M₄ H')
  + 10 p₃ (2 H M₂' - 9 M₂ H') - 144 H² p₁' N + 16 H² p₁ N'
  + 32 H² p₂' C - 8 H² p₂ C'`.

On the aligned face every right-hand correction vanishes, so
`H M₄' = 6 M₄ H'` and the weight-six polynomial first integral

`M₄ = κ₃ H⁶`

holds for a preserved constant `κ₃`.  The exponent is even, so — unlike
the odd ninth-power integral of the previous row — no square root of
`H` is needed and the integral itself is chamber-free.  The chambers of
the previous packets then specialize the consumed row honestly:

* square chamber `H = h₀²`, `p₃ = h₀ t`, `M₂ = μ h₀⁹`: cancelling `h₀⁴`
  leaves a chamber core whose `h₀`-free part is the pure fourth power
  `-5 t⁴`, so every root of the linear core kills `t` and the linear
  descent gives the NEW divisibility `t = h₀ u`, i.e. `p₃ = h₀² u` —
  the `p₃` jet vanishes doubly at the core root, one order deeper than
  the previous face's chamber-free kill.  Cancelling `h₀²` then solves
  the sextic row
  `128 q₆ = h₀² (240 p₂² + 120 p₂ u² - 5 u⁴ + 320 p₀ h₀⁴ + 480 p₁ u h₀²
  + κ (32 p₂ h₀² + 16 u² h₀²) - 14 μ u h₀³ - κ₃ h₀⁴)`; in particular
  `h₀² ∣ q₆`.  The previously solved coefficients upgrade to
  `q₉ = (5/2) u h₀⁸`, `8 q₈ = h₀⁶ (15 u² + 20 p₂ + κ h₀²)`, and
  `16 q₇ = h₀⁴ (5 u³ + 60 p₂ u + 40 p₁ h₀² + 4 κ u h₀² - μ h₀³)`.  The
  constants `μ` (with `μ² = κ₂`) and `κ₃` are preserved, not cleared.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`: cancelling `H³` solves the sextic row outright,
  `128 q₆ = H (320 p₀ H² + 480 p₁ g H + 240 p₂² + 120 p₂ g² - 5 g⁴
  + κ (32 p₂ H + 16 g² H) - κ₃ H²)`; in particular `H ∣ q₆`.  No new
  divisibility on `g` appears — the row is exactly absorbed by `q₆`.

Reused architecture: `squareCore_of_nonzero_imprimitiveRelation_410`
(through the previous face's chamber quotients
`ninthPower_squareChamber_form_410` and
`ninthPower_nonsquareChamber_kill_410`),
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` (tracked `(6,8)` aligned
architecture, generic in the degree pair),
`natDegree_one_dvd_of_root_kill_410`, and the previous faces' solved
forms.  The extended root jet is chamber-free through `q₆`: at a core
root `a` the values `p₃, q₉, q₈, q₇, q₆` and the derivatives `q₈', q₇'`
all vanish; the square chamber adds the honest second-order data
`p₃'(a) = 0` and `q₆'(a) = 0`.

No closure is claimed.  Both chambers remain open, the zero branches
(`u = 0`, `g = 0`, `t = 0`, `μ = 0`, `κ = 0`, `κ₂ = 0`, `κ₃ = 0`) are
not excluded, and the constants `κ`, `κ₂ = μ²`, `κ₃` are preserved
where not forced.  `p₀, p₁, p₂` are constrained only through the solved
forms.  The next unused Keller row on the aligned face is the
degree-`8` Jacobian coefficient, the first row that sees `q₅`.  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`9` Keller coefficient on the aligned face -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`9` Jacobian coefficient, the first
aligned row that sees `p₀` and `q₆`.  It is derived directly from the
Keller bracket. -/
theorem alignedFourthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 6).derivative +
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
        (7, 2), (8, 1), (9, 0)} :
        Finset (ℕ × ℕ)) := by decide
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
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned fourth defect -/

/-- Cleared fourth defect of the degree-`9` aligned `(4,10)` row, kept
in factored form through the third defect `M₂`:
`M₄ = 320 p₀ H⁶ - 128 q₆ H³ + 480 p₁ p₃ H⁴ + 240 p₂² H⁴
+ 120 p₂ p₃² H² - 5 p₃⁴ + κ (32 p₂ H⁵ + 16 p₃² H³) - 14 p₃ M₂`.  On
the aligned face it is a polynomial first integral of weight six. -/
def alignedFourthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b6 b7 : K[X]) (κ : K) : K[X] :=
  (320 : K[X]) * a0 * H ^ 6 - (128 : K[X]) * b6 * H ^ 3 +
    (480 : K[X]) * a1 * a3 * H ^ 4 + (240 : K[X]) * a2 ^ 2 * H ^ 4 +
    (120 : K[X]) * a2 * a3 ^ 2 * H ^ 2 - (5 : K[X]) * a3 ^ 4 +
    Polynomial.C κ *
      ((32 : K[X]) * a2 * H ^ 5 + (16 : K[X]) * a3 ^ 2 * H ^ 3) -
    (14 : K[X]) * a3 * alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`9` Jacobian expression with the
weighted derivative of `M₄`.  The corrections are the face residuals
`N = 5 p₃ H³ - 2 q₉` and `C = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴`, kept
factored, and the consumed degree-`10` bracket of `M₂`; every one of
them vanishes on the aligned face. -/
theorem alignedFourthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K] (H a0 a1 a2 a3 b6 b7 b8 b9 : K[X]) (κ : K) :
    (32 : K[X]) * H ^ 2 *
        ((H ^ 2).derivative * (b6 * (6 : K[X])) +
          a3.derivative * (b7 * (7 : K[X])) +
          a2.derivative * (b8 * (8 : K[X])) +
          a1.derivative * (b9 * (9 : K[X])) +
          a0.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b6.derivative +
          (a3 * (3 : K[X])) * b7.derivative +
          (a2 * (2 : K[X])) * b8.derivative +
          a1 * b9.derivative)) =
      (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
          (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
            H.derivative) +
        (10 : K[X]) * a3 *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) -
        (144 : K[X]) * H ^ 2 * a1.derivative *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9) +
        (16 : K[X]) * H ^ 2 * a1 *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9).derivative +
        (32 : K[X]) * H ^ 2 * a2.derivative *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H - Polynomial.C κ * H ^ 4) -
        (8 : K[X]) * H ^ 2 * a2 *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H -
            Polynomial.C κ * H ^ 4).derivative := by
  simp only [alignedFourthDefect410, alignedThirdDefect410,
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

/-- On the aligned face, with the consumed degree-`11` and degree-`10`
rows, the degree-`9` row is the weighted derivative
`H M₄' - 6 M₄ H' = 0`. -/
theorem alignedFourthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 6) (q.coeff 7) κ).derivative -
      (6 : K[X]) *
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedFourthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4, hq10] at hrow
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2] at hrow
  have hR :
      (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
          (15 : K[X]) * p.coeff 3 ^ 2 * H - Polynomial.C κ * H ^ 4 =
        0 := by
    have hM' :
        (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
            (15 : K[X]) * p.coeff 3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
      simpa only [alignedSecondDefect410] using hM
    linear_combination hM'
  have hDrow :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedFourthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 6)
    (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hR, hDrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-six polynomial first integral -/

/-- Generic Wronskian quotient for the weight-six bracket: over a
characteristic-zero field, `H D' - 6 D H' = 0` forces `D = C c * H⁶`.
The exponent is even, so the integral needs no square root of `H`. -/
theorem sixthPowerRelation_of_weightSixRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (6 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 6 := by
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hW : Polynomial.wronskian D (H ^ 6) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (6 : K) * H ^ (6 - 1) * H.derivative) -
          D.derivative * H ^ 6 =
          H ^ 5 *
            (Polynomial.C (6 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC6]
        have hfac :
            (6 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 6 hH) hW

/-- Weight-six polynomial first integral of the aligned `(4,10)` fourth
defect: `M₄ = κ₃ H⁶`.  The even exponent makes the integral chamber-free
— no square root of `H` is required. -/
theorem alignedFourthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₃ : K,
      alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₃ * H ^ 6 :=
  sixthPowerRelation_of_weightSixRow_410 hH
    (alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Generic double-factor derivative kill -/

/-- The derivative of any polynomial carrying an at-least-squared factor
vanishes at every root of that factor. -/
theorem derivative_eval_eq_zero_of_pow_factor_410 {K : Type*}
    [CommRing K] {h g B : K[X]} {n : ℕ} (hn : 2 ≤ n)
    (hg : g = h ^ n * B) {a : K} (ha : h.eval a = 0) :
    g.derivative.eval a = 0 := by
  rw [hg, Polynomial.derivative_mul, Polynomial.derivative_pow]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, ha]
  rw [zero_pow (by omega : n - 1 ≠ 0), zero_pow (by omega : n ≠ 0)]
  ring

/-! ## Square chamber -/

/-- Cleared square-core form of the fourth defect relation: cancelling
`h₀⁴` from `M₄ = κ₃ h₀¹²` on `p₃ = h₀ t`, `M₂ = μ h₀⁹` leaves the
degree-`8` chamber core whose `h₀`-free part is the pure fourth power
`-5 t⁴`. -/
theorem alignedSquareFourth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 t a0 a1 a2 a3 b6 b7 : K[X]} {κ μ κ₃ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 * t)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6) :
    (320 : K[X]) * a0 * h0 ^ 8 - (128 : K[X]) * b6 * h0 ^ 2 +
        (480 : K[X]) * a1 * t * h0 ^ 5 + (240 : K[X]) * a2 ^ 2 * h0 ^ 4 +
        (120 : K[X]) * a2 * t ^ 2 * h0 ^ 2 - (5 : K[X]) * t ^ 4 +
        Polynomial.C κ *
          ((32 : K[X]) * a2 * h0 ^ 6 + (16 : K[X]) * t ^ 2 * h0 ^ 4) -
        Polynomial.C μ * ((14 : K[X]) * t * h0 ^ 6) =
      Polynomial.C κ₃ * h0 ^ 8 := by
  have hM4' := hM4
  simp only [alignedFourthDefect410] at hM4'
  rw [hM2, hHsq, hp3] at hM4'
  apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
  linear_combination hM4'

/-- The consumed degree-`9` row in the square chamber: the `h₀`-free
part of the chamber core is `-5 t⁴`, so the linear descent forces the
NEW divisibility `t = h₀ u` — the `p₃` jet vanishes doubly at the core
root — and cancelling `h₀²` solves the sextic row against the preserved
constants `μ` and `κ₃`. -/
theorem alignedSquareFourth_descent_410 {K : Type*} [Field K] [CharZero K]
    {h0 t a0 a1 a2 b6 : K[X]} {κ μ κ₃ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hcore :
      (320 : K[X]) * a0 * h0 ^ 8 - (128 : K[X]) * b6 * h0 ^ 2 +
          (480 : K[X]) * a1 * t * h0 ^ 5 +
          (240 : K[X]) * a2 ^ 2 * h0 ^ 4 +
          (120 : K[X]) * a2 * t ^ 2 * h0 ^ 2 - (5 : K[X]) * t ^ 4 +
          Polynomial.C κ *
            ((32 : K[X]) * a2 * h0 ^ 6 + (16 : K[X]) * t ^ 2 * h0 ^ 4) -
          Polynomial.C μ * ((14 : K[X]) * t * h0 ^ 6) =
        Polynomial.C κ₃ * h0 ^ 8) :
    ∃ u : K[X], t = h0 * u ∧
      (128 : K[X]) * b6 =
        h0 ^ 2 * ((240 : K[X]) * a2 ^ 2 + (120 : K[X]) * a2 * u ^ 2 -
          (5 : K[X]) * u ^ 4 + (320 : K[X]) * a0 * h0 ^ 4 +
          (480 : K[X]) * a1 * u * h0 ^ 2 +
          Polynomial.C κ *
            ((32 : K[X]) * a2 * h0 ^ 2 + (16 : K[X]) * u ^ 2 * h0 ^ 2) -
          Polynomial.C μ * ((14 : K[X]) * u * h0 ^ 3) -
          Polynomial.C κ₃ * h0 ^ 4) := by
  have ht4 : (5 : K[X]) * t ^ 4 =
      h0 ^ 2 * ((320 : K[X]) * a0 * h0 ^ 6 - (128 : K[X]) * b6 +
        (480 : K[X]) * a1 * t * h0 ^ 3 + (240 : K[X]) * a2 ^ 2 * h0 ^ 2 +
        (120 : K[X]) * a2 * t ^ 2 +
        Polynomial.C κ *
          ((32 : K[X]) * a2 * h0 ^ 4 + (16 : K[X]) * t ^ 2 * h0 ^ 2) -
        Polynomial.C μ * ((14 : K[X]) * t * h0 ^ 4) -
        Polynomial.C κ₃ * h0 ^ 6) := by
    linear_combination -hcore
  have hkill : ∀ a : K, h0.eval a = 0 → t.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) ht4
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [ha, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (5 : K) ≠ 0))
  obtain ⟨u, hu⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill
  refine ⟨u, hu, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
  rw [hu] at hcore
  linear_combination -hcore

/-! ## Nonsquare chamber -/

/-- The consumed degree-`9` row in the nonsquare chamber: with the
vanished third defect and the simple-root divisibility `p₃ = H g`, the
weight-six integral solves the sextic coefficient outright with an
explicit `H` factor. -/
theorem alignedNonsquareFourth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b6 b7 : K[X]} {κ κ₃ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6) :
    (128 : K[X]) * b6 =
      H * ((320 : K[X]) * a0 * H ^ 2 + (480 : K[X]) * a1 * g * H +
        (240 : K[X]) * a2 ^ 2 + (120 : K[X]) * a2 * g ^ 2 -
        (5 : K[X]) * g ^ 4 +
        Polynomial.C κ *
          ((32 : K[X]) * a2 * H + (16 : K[X]) * g ^ 2 * H) -
        Polynomial.C κ₃ * H ^ 2) := by
  have hM4' := hM4
  simp only [alignedFourthDefect410] at hM4'
  rw [hM20, hg] at hM4'
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination -hM4'

/-! ## Source-facing fourth-row packets -/

/-- Source-facing weight-six integral of a normalized aligned scale-two
`(4,10)` source: the degree-`9` row is consumed into `M₄ = κ₃ H⁶` on
top of the previous aligned packet, chamber-free, together with the
chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedFourthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₂ * H ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        ∀ a : K, H.eval a = 0 →
          (p.coeff 3).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber fourth packet of a normalized aligned scale-two
`(4,10)` source: the NEW second-order divisibility `p₃ = h₀² u`, the
solved sextic row `128 q₆ = h₀² (240 p₂² + 120 p₂ u² - 5 u⁴ + 320 p₀ h₀⁴
+ 480 p₁ u h₀² + κ (32 p₂ h₀² + 16 u² h₀²) - 14 μ u h₀³ - κ₃ h₀⁴)`, and
the upgraded solved forms `q₉ = (5/2) u h₀⁸`,
`8 q₈ = h₀⁶ (15 u² + 20 p₂ + κ h₀²)`, and
`16 q₇ = h₀⁴ (5 u³ + 60 p₂ u + 40 p₁ h₀² + 4 κ u h₀² - μ h₀³)`.  The
constants `μ` and `κ₃` are preserved, not cleared. -/
theorem normalized410ScaleTwo_alignedFourthRow_squareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ : K) (u : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        q.coeff 9 = Polynomial.C (5 / 2 : K) * u * h0 ^ 8 ∧
        (8 : K[X]) * q.coeff 8 =
          h0 ^ 6 * ((15 : K[X]) * u ^ 2 + (20 : K[X]) * p.coeff 2 +
            Polynomial.C κ * h0 ^ 2) ∧
        (16 : K[X]) * q.coeff 7 =
          h0 ^ 4 * ((5 : K[X]) * u ^ 3 +
            (60 : K[X]) * p.coeff 2 * u +
            (40 : K[X]) * p.coeff 1 * h0 ^ 2 +
            (4 : K[X]) * Polynomial.C κ * u * h0 ^ 2 -
            Polynomial.C μ * h0 ^ 3) ∧
        (128 : K[X]) * q.coeff 6 =
          h0 ^ 2 * ((240 : K[X]) * p.coeff 2 ^ 2 +
            (120 : K[X]) * p.coeff 2 * u ^ 2 -
            (5 : K[X]) * u ^ 4 + (320 : K[X]) * p.coeff 0 * h0 ^ 4 +
            (480 : K[X]) * p.coeff 1 * u * h0 ^ 2 +
            Polynomial.C κ *
              ((32 : K[X]) * p.coeff 2 * h0 ^ 2 +
                (16 : K[X]) * u ^ 2 * h0 ^ 2) -
            Polynomial.C μ * ((14 : K[X]) * u * h0 ^ 3) -
            Polynomial.C κ₃ * h0 ^ 4) ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hDform⟩ :=
    ninthPower_squareChamber_form_410 hH hHsq hrel
  have hdeg1 : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hHdegree, Polynomial.natDegree_pow] at hdegree
    omega
  have hkill0 : ∀ a : K, h0.eval a = 0 → (p.coeff 3).eval a = 0 := by
    intro a ha
    apply alignedThird_rootKill_p3_410 hrel
    rw [hHsq]
    simp only [Polynomial.eval_pow, ha]
    norm_num
  obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
  obtain ⟨u, hu, hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
  have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = Polynomial.C μ * h0 ^ 9 := by
    simpa only [alignedThirdDefect410] using hDform
  refine ⟨κ, μ, κ₃, u, hp3, hDform, ?_, ?_, ?_, hq6, hM4⟩
  · rw [hq9, hp3, hHsq]; ring
  · rw [hp3, hHsq] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ (pow_ne_zero 2 hh0)
    rw [hp3, hHsq] at hD'
    linear_combination -hD'

/-- Exact nonsquare-chamber fourth packet of a normalized aligned
scale-two `(4,10)` source: the previous packet plus the solved sextic
row `128 q₆ = H (320 p₀ H² + 480 p₁ g H + 240 p₂² + 120 p₂ g² - 5 g⁴
+ κ (32 p₂ H + 16 g² H) - κ₃ H²)`; in particular `H ∣ q₆`.  No new
divisibility on `g` appears. -/
theorem normalized410ScaleTwo_alignedFourthRow_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ : K) (g : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        q.coeff 9 = Polynomial.C (5 / 2 : K) * g * H ^ 4 ∧
        (8 : K[X]) * q.coeff 8 =
          H ^ 3 * ((15 : K[X]) * g ^ 2 + (20 : K[X]) * p.coeff 2 +
            Polynomial.C κ * H) ∧
        (16 : K[X]) * q.coeff 7 =
          H ^ 2 * ((5 : K[X]) * g ^ 3 + (60 : K[X]) * p.coeff 2 * g +
            (40 : K[X]) * p.coeff 1 * H +
            (4 : K[X]) * Polynomial.C κ * g * H) ∧
        (128 : K[X]) * q.coeff 6 =
          H * ((320 : K[X]) * p.coeff 0 * H ^ 2 +
            (480 : K[X]) * p.coeff 1 * g * H +
            (240 : K[X]) * p.coeff 2 ^ 2 +
            (120 : K[X]) * p.coeff 2 * g ^ 2 -
            (5 : K[X]) * g ^ 4 +
            Polynomial.C κ *
              ((32 : K[X]) * p.coeff 2 * H +
                (16 : K[X]) * g ^ 2 * H) -
            Polynomial.C κ₃ * H ^ 2) ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_410 hp hq hjac hH hp4' hq10' haligned
  obtain ⟨κ₂, hrel⟩ :=
    alignedThirdDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₂, hD0⟩ :=
    ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq ha
  have hkill : ∀ a : K, H.eval a = 0 → (p.coeff 3).eval a = 0 :=
    fun a ha => alignedThird_rootKill_p3_410 hrel ha
  obtain ⟨g, hg⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
  obtain ⟨κ₃, hM4⟩ :=
    alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hq6 := alignedNonsquareFourth_solved_410 hH hg hD0 hM4
  have hq9 := aligned_q9_solved_410 haligned
  have hclear := alignedSecondDefect_clearing_410 hM
  have hD0' :
      (5 : K[X]) * p.coeff 3 ^ 3 +
            (60 : K[X]) * p.coeff 2 * p.coeff 3 * H ^ 2 +
            (40 : K[X]) * p.coeff 1 * H ^ 4 +
            (4 : K[X]) * Polynomial.C κ * p.coeff 3 * H ^ 3 -
          (16 : K[X]) * q.coeff 7 * H = 0 := by
    simpa only [alignedThirdDefect410] using hD0
  refine ⟨κ, κ₃, g, hg, hD0, ?_, ?_, ?_, hq6, hM4⟩
  · rw [hq9, hg]; ring
  · rw [hg] at hclear
    linear_combination hclear
  · apply mul_right_cancel₀ hH
    rw [hg] at hD0'
    linear_combination -hD0'

/-- Honest square/nonsquare chamber split of the consumed degree-`9`
aligned row.  Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedFourthRow_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ κ₃ : K) (u : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          q.coeff 9 = Polynomial.C (5 / 2 : K) * u * h0 ^ 8 ∧
          (8 : K[X]) * q.coeff 8 =
            h0 ^ 6 * ((15 : K[X]) * u ^ 2 + (20 : K[X]) * p.coeff 2 +
              Polynomial.C κ * h0 ^ 2) ∧
          (16 : K[X]) * q.coeff 7 =
            h0 ^ 4 * ((5 : K[X]) * u ^ 3 +
              (60 : K[X]) * p.coeff 2 * u +
              (40 : K[X]) * p.coeff 1 * h0 ^ 2 +
              (4 : K[X]) * Polynomial.C κ * u * h0 ^ 2 -
              Polynomial.C μ * h0 ^ 3) ∧
          (128 : K[X]) * q.coeff 6 =
            h0 ^ 2 * ((240 : K[X]) * p.coeff 2 ^ 2 +
              (120 : K[X]) * p.coeff 2 * u ^ 2 -
              (5 : K[X]) * u ^ 4 + (320 : K[X]) * p.coeff 0 * h0 ^ 4 +
              (480 : K[X]) * p.coeff 1 * u * h0 ^ 2 +
              Polynomial.C κ *
                ((32 : K[X]) * p.coeff 2 * h0 ^ 2 +
                  (16 : K[X]) * u ^ 2 * h0 ^ 2) -
              Polynomial.C μ * ((14 : K[X]) * u * h0 ^ 3) -
              Polynomial.C κ₃ * h0 ^ 4) ∧
          alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₃ * H ^ 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₃ : K) (g : K[X]),
        p.coeff 3 = H * g ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = 0 ∧
          q.coeff 9 = Polynomial.C (5 / 2 : K) * g * H ^ 4 ∧
          (8 : K[X]) * q.coeff 8 =
            H ^ 3 * ((15 : K[X]) * g ^ 2 + (20 : K[X]) * p.coeff 2 +
              Polynomial.C κ * H) ∧
          (16 : K[X]) * q.coeff 7 =
            H ^ 2 * ((5 : K[X]) * g ^ 3 +
              (60 : K[X]) * p.coeff 2 * g +
              (40 : K[X]) * p.coeff 1 * H +
              (4 : K[X]) * Polynomial.C κ * g * H) ∧
          (128 : K[X]) * q.coeff 6 =
            H * ((320 : K[X]) * p.coeff 0 * H ^ 2 +
              (480 : K[X]) * p.coeff 1 * g * H +
              (240 : K[X]) * p.coeff 2 ^ 2 +
              (120 : K[X]) * p.coeff 2 * g ^ 2 -
              (5 : K[X]) * g ^ 4 +
              Polynomial.C κ *
                ((32 : K[X]) * p.coeff 2 * H +
                  (16 : K[X]) * g ^ 2 * H) -
              Polynomial.C κ₃ * H ^ 2) ∧
          alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₃ * H ^ 6) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    exact Or.inl ⟨h0, hh0, hHsq,
      normalized410ScaleTwo_alignedFourthRow_squareChamber_packet
        hsource hh0 hHsq haligned⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    exact Or.inr ⟨hnsq,
      normalized410ScaleTwo_alignedFourthRow_nonsquareChamber_packet
        hsource hnsq haligned⟩

/-- Extended root data of the consumed degree-`9` row: at scale two the
common core has a root where the full jet `p₃, q₉, q₈, q₇, q₆` vanishes
with `q₈` and `q₇` vanishing to second order, chamber-free; the square
chamber adds the honest second-order data `p₃'(a) = 0` and `q₆'(a) = 0`
through the new divisibility `p₃ = h₀² u`. -/
theorem normalized410ScaleTwo_alignedFourthRow_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 3).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 ∧
      (q.coeff 7).eval a = 0 ∧
      (q.coeff 7).derivative.eval a = 0 ∧
      (q.coeff 6).eval a = 0 ∧
      ((∃ h0 u : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          (q.coeff 6).derivative.eval a = 0) ∨
        (∀ h0 : K[X], H ≠ h0 ^ 2)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedFourthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, u, hp3, _hM2f, hq9, hq8, hq7, hq6, _hM4⟩ := hpacket
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hp3d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        P).coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hq8d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 8).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 6) hq8 hroot
      have h8 : (8 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 8).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)
    have hq7d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 7).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 4) hq7 hroot
      have h16 : (16 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 7).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h16).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    have hq6d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 6).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hq6 hroot
      have h128 : (128 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 6).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h128).resolve_left
        (by norm_num : (128 : K) ≠ 0)
    refine ⟨a, ?_, ?_, ?_, ?_, hq8d, ?_, hq7d, ?_,
      Or.inl ⟨h0, u, hh0, hHsq, hroot, hp3, hp3d, hq6d⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (8 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (6 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (8 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (128 : K) ≠ 0)
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedFourthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, g, hp3, _hM20, hq9, hq8, hq7, hq6, _hM4⟩ := hpacket
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hq8d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 8).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 3) hq8 hroot
      have h8 : (8 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 8).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h8).resolve_left (by norm_num : (8 : K) ≠ 0)
    have hq7d : (((Polynomial.Bivariate.equivMvPolynomial K).symm
        Q).coeff 7).derivative.eval a = 0 := by
      have hfull := derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hq7 hroot
      have h16 : (16 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 7).derivative.eval a = 0 := by
        simpa only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
          zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
          using hfull
      exact (mul_eq_zero.mp h16).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    refine ⟨a, hroot, ?_, ?_, ?_, hq8d, ?_, hq7d, ?_, Or.inr hnsq⟩
    · rw [hp3, Polynomial.eval_mul, hroot, zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (8 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (16 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (128 : K) ≠ 0)

#print axioms alignedFourthCoefficientJacobianRow_410
#print axioms alignedFourthDefect_weightedDerivative_identity_410
#print axioms alignedFourthDefectRow_eq_zero_410
#print axioms sixthPowerRelation_of_weightSixRow_410
#print axioms alignedFourthDefectPowerRelation_410
#print axioms derivative_eval_eq_zero_of_pow_factor_410
#print axioms alignedSquareFourth_core_410
#print axioms alignedSquareFourth_descent_410
#print axioms alignedNonsquareFourth_solved_410
#print axioms normalized410ScaleTwo_alignedFourthRow_packet
#print axioms normalized410ScaleTwo_alignedFourthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedFourthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedFourthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedFourthRow_rootData

end Max11DegreeRoutes
