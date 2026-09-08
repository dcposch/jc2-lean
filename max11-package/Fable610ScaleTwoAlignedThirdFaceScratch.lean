import Fable610ScaleTwoAlignedFaceScratch
import LowScale810ScaleTwoThirdFace

/-! # Third aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedFaceScratch` opened the aligned face `N = 0` of
the normalized scale-two `(6,10)` source and consumed the degree-`13`
Keller row: `q₉ = (5/3) p₅ H²`, the weight-five polynomial first
integral `M = 9 q₈ H - 15 p₄ H³ - 5 p₅² = κ H⁵`, and the honest
square/nonsquare chamber split.  This file consumes the next unused
aligned row, the degree-`12` Jacobian coefficient — the first row that
sees `p₃` and `q₇`.

At the common source level, modulo the face `N = 5 p₅ H² - 3 q₉ = 0`
and the consumed degree-`13` relation
`C = 9 q₈ H - 15 p₄ H³ - 5 p₅² - κ H⁵ = 0`, the degree-`12` row is the
weighted derivative of the cleared half-weight defect

`D = 135 p₃ H⁶ - 81 q₇ H⁴ + 90 p₄ p₅ H³ - 5 p₅³ + 12 κ p₅ H⁵`,

via the exact multiplier identity

`27 H² · row₁₂[p₆ = H³, q₁₀ = H⁵] = (2 H D' - 15 D H')
  - 81 H² p₄' N + 36 H² p₄ N' + (24 H p₅' + 15 p₅ H') C - 15 H p₅ C'`.

On the aligned face every right-hand correction vanishes, so
`2 H D' = 15 D H'` and the squared weight-fifteen first integral

`D² = κ₂ H¹⁵`

holds for a preserved constant `κ₂`.  The odd exponent splits honestly
on the chambers of the previous packet:

* square chamber `H = h₀²`, `p₅ = h₀ g`: the integral has a polynomial
  square root `D = μ h₀¹⁵` with `μ² = κ₂`, and a two-step descent at the
  root of the linear core gives `g = h₀² w`; hence `p₅ = h₀³ w`,
  `q₉ = (5/3) w h₀⁷`, `9 q₈ = h₀⁴ (5 w² + 15 p₄ + κ h₀⁴)`, and the new
  solved septic row
  `81 q₇ = h₀ (135 p₃ h₀³ + 90 p₄ w - 5 w³ + 12 κ w h₀⁴ - μ h₀⁶)`;
  in particular `h₀ ∣ q₇`.  The constant `μ` is preserved, not cleared.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₂ = 0` and `D = 0` identically; the simple-root
  descent gives `g = H g₁`, hence `p₅ = H² g₁`, `q₉ = (5/3) g₁ H⁴`,
  `9 q₈ = H² (5 H g₁² + 15 p₄ + κ H²)`, and
  `81 q₇ = H (135 p₃ H + 90 p₄ g₁ - 5 H g₁³ + 12 κ g₁ H²)`;
  in particular `H² ∣ p₅` and `H ∣ q₇`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` from the `(6,8)` aligned
architecture, `dvd_of_sq_dvd_sq_poly`, and
`linearPolynomial_dvd_of_eval_eq_zero_810` from the `(8,10)` chain (all
generic in the degree pair).  The chamber-independent root jet extends
to `q₈` and `q₇`: at a root of `H` the coefficients `p₅, q₉, q₈, q₇`
all vanish.

No closure is claimed.  Both chambers remain open, the zero branches
(`g = 0`, `w = 0`, `g₁ = 0`, `κ = 0`, `κ₂ = 0`, `μ = 0`) are not
excluded, and the constants `κ`, `κ₂ = μ²` are preserved where not
forced.  The next unused Keller row on the aligned face is the
degree-`11` Jacobian coefficient, the first row that sees `p₂` and
`q₆`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`12` Keller coefficient on the aligned face -/

/-- The third row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`12` Jacobian coefficient, the first
aligned row that sees `p₃` and `q₇`. -/
theorem alignedThirdCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) *
          (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 12) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1),
        (12, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC7, hC8, hC9, hC10, hC6, hC5, hC4, hC3]
  linear_combination hcoeff

/-! ## Aligned third defect -/

/-- Cleared half-weight defect of the degree-`12` aligned `(6,10)` row:
`D = 135 p₃ H⁶ - 81 q₇ H⁴ + 90 p₄ p₅ H³ - 5 p₅³ + 12 κ p₅ H⁵`.  On the
aligned face its square is a polynomial first integral of weight
fifteen. -/
def alignedThirdDefect610 {K : Type*} [CommRing K]
    (H a3 a4 a5 b7 : K[X]) (κ : K) : K[X] :=
  (135 : K[X]) * a3 * H ^ 6 - (81 : K[X]) * b7 * H ^ 4 +
    (90 : K[X]) * a4 * a5 * H ^ 3 - (5 : K[X]) * a5 ^ 3 +
    Polynomial.C κ * ((12 : K[X]) * a5 * H ^ 5)

set_option maxHeartbeats 64000000 in
/-- Exact combination of the degree-`12` Jacobian expression with the
weighted derivative of `D`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` row. -/
theorem alignedThirdDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K] (H a3 a4 a5 b7 b8 b9 : K[X]) (κ : K) :
    (27 : K[X]) * H ^ 2 *
        ((H ^ 3).derivative * (b7 * (7 : K[X])) +
          a5.derivative * (b8 * (8 : K[X])) +
          a4.derivative * (b9 * (9 : K[X])) +
          a3.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b7.derivative +
          (a5 * (5 : K[X])) * b8.derivative +
          (a4 * (4 : K[X])) * b9.derivative +
          (a3 * (3 : K[X])) * (H ^ 5).derivative)) =
      ((2 : K[X]) * H *
          (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
        (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
          H.derivative) -
        (81 : K[X]) * H ^ 2 * a4.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) +
        (36 : K[X]) * H ^ 2 * a4 *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9).derivative +
        ((24 : K[X]) * H * a5.derivative +
            (15 : K[X]) * a5 * H.derivative) *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) -
        (15 : K[X]) * H * a5 *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 -
            Polynomial.C κ * H ^ 5).derivative := by
  simp only [alignedThirdDefect610, Polynomial.derivative_sub,
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

/-- On the aligned face, with the consumed degree-`13` integral, the
degree-`12` row is the weighted derivative `2 H D' - 15 D H' = 0`. -/
theorem alignedThirdDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H *
        (alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (q.coeff 7) κ).derivative -
      (15 : K[X]) *
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedThirdCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  rw [hC7, hC8, hC9, hC10, hC6, hC5, hC4, hC3] at hrow
  have hC0 :
      (9 : K[X]) * q.coeff 8 * H - (15 : K[X]) * p.coeff 4 * H ^ 3 -
          (5 : K[X]) * p.coeff 5 ^ 2 - Polynomial.C κ * H ^ 5 = 0 := by
    have hM' :
        (9 : K[X]) * q.coeff 8 * H - (15 : K[X]) * p.coeff 4 * H ^ 3 -
            (5 : K[X]) * p.coeff 5 ^ 2 = Polynomial.C κ * H ^ 5 := by
      simpa only [alignedSecondDefect610] using hM
    linear_combination hM'
  have hid := alignedThirdDefect_weightedDerivative_identity_610
    H (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 7) (q.coeff 8)
    (q.coeff 9) κ
  rw [hrow, haligned, hC0] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-fifteen polynomial first integral of the aligned
`(6,10)` third defect: `D² = κ₂ H¹⁵`. -/
theorem alignedThirdDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₂ : K,
      alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₂ * H ^ 15 := by
  let D : K[X] :=
    alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * D.derivative -
        (15 : K[X]) * D * H.derivative = 0 := by
    simpa only [D] using
      alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC15 : Polynomial.C (15 : K) = (15 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 15) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (15 : K) * H ^ (15 - 1) * H.derivative) -
          Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative * H ^ 15 =
          D * H ^ 14 *
            (Polynomial.C (15 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by
        ring
      _ = 0 := by
        rw [hC15, hC2]
        have hfac :
            (15 : K[X]) * D * H.derivative -
              (2 : K[X]) * H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 15 hH) hW

/-! ## Square chamber -/

/-- In the square chamber the weight-fifteen integral has a polynomial
square root with square core: `D = μ h₀¹⁵` with `μ² = κ₂`.  The constant
`μ` is preserved, not cleared. -/
theorem alignedSquareThird_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a3 a4 a5 b7 : K[X]} {κ κ₂ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hD2 : alignedThirdDefect610 H a3 a4 a5 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 15) :
    ∃ μ : K, μ ^ 2 = κ₂ ∧
      alignedThirdDefect610 H a3 a4 a5 b7 κ =
        Polynomial.C μ * h0 ^ 15 := by
  set D : K[X] := alignedThirdDefect610 H a3 a4 a5 b7 κ
  have hdvd : (h0 ^ 15) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C κ₂, ?_⟩
    rw [hD2, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C κ₂ := by
    have h30 := hD2
    rw [hF, hHsq] at h30
    apply mul_left_cancel₀ (pow_ne_zero 30 hh0)
    linear_combination h30
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C κ₂
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ, hμ⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ ^ 2) = Polynomial.C κ₂ := by
      rw [Polynomial.C_pow, hμ, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ]
    ring

/-- Cleared square-core form of the third defect relation: cancelling
`h₀³` from `D = μ h₀¹⁵` on `p₅ = h₀ g` leaves the degree-`12`
chamber core `E = μ h₀¹²`. -/
theorem alignedSquareThird_core_610 {K : Type*} [Field K] [CharZero K]
    {H h0 g a3 a4 a5 b7 : K[X]} {κ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a5 = h0 * g)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15) :
    (135 : K[X]) * a3 * h0 ^ 9 - (81 : K[X]) * b7 * h0 ^ 5 +
        (90 : K[X]) * a4 * g * h0 ^ 4 - (5 : K[X]) * g ^ 3 +
        Polynomial.C κ * ((12 : K[X]) * g * h0 ^ 8) =
      Polynomial.C μ * h0 ^ 12 := by
  have hD' :
      (135 : K[X]) * a3 * (h0 ^ 2) ^ 6 -
          (81 : K[X]) * b7 * (h0 ^ 2) ^ 4 +
          (90 : K[X]) * a4 * (h0 * g) * (h0 ^ 2) ^ 3 -
          (5 : K[X]) * (h0 * g) ^ 3 +
          Polynomial.C κ * ((12 : K[X]) * (h0 * g) * (h0 ^ 2) ^ 5) =
        Polynomial.C μ * h0 ^ 15 := by
    simpa only [alignedThirdDefect610, hHsq, hg] using hD
  apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
  linear_combination hD'

/-- Two-step descent at the root of the linear square core: the chamber
core relation forces `h₀² ∣ g` and solves the septic coefficient with an
explicit `h₀` factor. -/
theorem alignedSquareThird_descent_610 {K : Type*} [Field K] [CharZero K]
    {h0 g a3 a4 b7 : K[X]} {κ μ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hE : (135 : K[X]) * a3 * h0 ^ 9 - (81 : K[X]) * b7 * h0 ^ 5 +
        (90 : K[X]) * a4 * g * h0 ^ 4 - (5 : K[X]) * g ^ 3 +
        Polynomial.C κ * ((12 : K[X]) * g * h0 ^ 8) =
      Polynomial.C μ * h0 ^ 12) :
    ∃ w : K[X], g = h0 ^ 2 * w ∧
      (81 : K[X]) * b7 =
        h0 * ((135 : K[X]) * a3 * h0 ^ 3 + (90 : K[X]) * a4 * w -
          (5 : K[X]) * w ^ 3 +
          Polynomial.C κ * ((12 : K[X]) * w * h0 ^ 4) -
          Polynomial.C μ * h0 ^ 6) := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hg3 : (5 : K[X]) * g ^ 3 =
      h0 * ((135 : K[X]) * a3 * h0 ^ 8 - (81 : K[X]) * b7 * h0 ^ 4 +
        (90 : K[X]) * a4 * g * h0 ^ 3 +
        Polynomial.C κ * ((12 : K[X]) * g * h0 ^ 7) -
        Polynomial.C μ * h0 ^ 11) := by
    linear_combination -hE
  have hgroot : g.eval (-(d / c)) = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval (-(d / c))) hg3
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [hroot, zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (5 : K) ≠ 0))
  obtain ⟨g1, hg1⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 g (-(d / c)) hdeg1
      hroot hgroot
  have hg13 : (5 : K[X]) * g1 ^ 3 =
      h0 * ((135 : K[X]) * a3 * h0 ^ 5 - (81 : K[X]) * b7 * h0 +
        (90 : K[X]) * a4 * g1 * h0 +
        Polynomial.C κ * ((12 : K[X]) * g1 * h0 ^ 5) -
        Polynomial.C μ * h0 ^ 8) := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hg1] at hg3
    linear_combination hg3
  have hg1root : g1.eval (-(d / c)) = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval (-(d / c))) hg13
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [hroot, zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (5 : K) ≠ 0))
  obtain ⟨w, hw⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 g1 (-(d / c)) hdeg1
      hroot hg1root
  have hgw : g = h0 ^ 2 * w := by
    rw [hg1, hw]; ring
  refine ⟨w, hgw, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 5 hh0)
  rw [hgw] at hE
  linear_combination -hE

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the weight-fifteen
integral forces its constant to vanish, and with it the whole third
defect. -/
theorem alignedNonsquareThird_defect_eq_zero_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a3 a4 a5 b7 : k[X]} {κ κ₂ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hD2 : alignedThirdDefect610 H a3 a4 a5 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 15) :
    κ₂ = 0 ∧ alignedThirdDefect610 H a3 a4 a5 b7 κ = 0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set D : k[X] := alignedThirdDefect610 H a3 a4 a5 b7 κ
  have hdvd : (H ^ 7) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C κ₂ * H, ?_⟩
    rw [hD2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₂ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hH)
    have h14 := hD2
    rw [hG] at h14
    linear_combination h14
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₂ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk2 : κ₂ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hDzero : D = 0 := by
    have hsq : D ^ 2 = 0 := by
      rw [hD2, hk2]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk2, hDzero⟩

/-- Simple-root descent of the vanished third defect: `H ∣ g`, and the
septic coefficient is solved with an explicit `H` factor. -/
theorem alignedNonsquareThird_solved_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g a3 a4 a5 b7 : k[X]} {κ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hg : a5 = H * g)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0) :
    ∃ g1 : k[X], g = H * g1 ∧
      (81 : k[X]) * b7 =
        H * ((135 : k[X]) * a3 * H + (90 : k[X]) * a4 * g1 -
          (5 : k[X]) * H * g1 ^ 3 +
          Polynomial.C κ * ((12 : k[X]) * g1 * H ^ 2)) := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hD0' :
      (135 : k[X]) * a3 * H ^ 6 - (81 : k[X]) * b7 * H ^ 4 +
          (90 : k[X]) * a4 * (H * g) * H ^ 3 -
          (5 : k[X]) * (H * g) ^ 3 +
          Polynomial.C κ * ((12 : k[X]) * (H * g) * H ^ 5) = 0 := by
    simpa only [alignedThirdDefect610, hg] using hD0
  have hEn :
      (135 : k[X]) * a3 * H ^ 3 - (81 : k[X]) * b7 * H +
          (90 : k[X]) * a4 * g * H - (5 : k[X]) * g ^ 3 +
          Polynomial.C κ * ((12 : k[X]) * g * H ^ 3) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hH)
    rw [mul_zero]
    linear_combination hD0'
  have hg3 : (5 : k[X]) * g ^ 3 =
      H * ((135 : k[X]) * a3 * H ^ 2 - (81 : k[X]) * b7 +
        (90 : k[X]) * a4 * g +
        Polynomial.C κ * ((12 : k[X]) * g * H ^ 2)) := by
    linear_combination -hEn
  have hgroot : ∀ a : k, H.eval a = 0 → g.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hg3
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [ha, zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (5 : k) ≠ 0))
  obtain ⟨g1, hg1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hgroot
  refine ⟨g1, hg1, ?_⟩
  have h2 : H * (H * ((135 : k[X]) * a3 * H + (90 : k[X]) * a4 * g1 -
      (5 : k[X]) * H * g1 ^ 3 +
      Polynomial.C κ * ((12 : k[X]) * g1 * H ^ 2)) -
      (81 : k[X]) * b7) = 0 := by
    rw [hg1] at hEn
    linear_combination hEn
  have h3 := (mul_eq_zero.mp h2).resolve_left hH
  linear_combination -h3

/-! ## Source-facing third-row packets -/

/-- Source-facing squared weight-fifteen integral of a normalized
aligned scale-two `(6,10)` source: the degree-`12` row is consumed into
`D² = κ₂ H¹⁵` on top of the previous aligned packet. -/
theorem normalized610ScaleTwo_alignedThirdFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ : K),
      q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₂ * H ^ 15 := by
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
  exact ⟨κ, κ₂, aligned_q9_solved_610 haligned, hM, hD2⟩

/-- Exact square-chamber third packet of a normalized aligned scale-two
`(6,10)` source: `p₅ = h₀³ w`, `q₉ = (5/3) w h₀⁷`,
`9 q₈ = h₀⁴ (5 w² + 15 p₄ + κ h₀⁴)`, the solved septic row
`81 q₇ = h₀ (135 p₃ h₀³ + 90 p₄ w - 5 w³ + 12 κ w h₀⁴ - μ h₀⁶)`, and
the square root `D = μ h₀¹⁵` of the weight-fifteen integral. -/
theorem normalized610ScaleTwo_alignedThirdFace_squareChamber_packet
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
    ∃ (κ μ : K) (w : K[X]),
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
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 := by
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
  have hE := alignedSquareThird_core_610 hh0 hHsq hg hD
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨w, hgw, hq7⟩ := alignedSquareThird_descent_610 hh0 hdeg1 hE
  refine ⟨κ, μ, w, ?_, ?_, ?_, hq7, hD⟩
  · rw [hg, hgw]; ring
  · rw [hq9, hg, hgw, hHsq]; ring
  · rw [hq8, hgw]; ring

/-- Exact nonsquare-chamber third packet of a normalized aligned
scale-two `(6,10)` source: the weight-fifteen constant vanishes, the
third defect is identically zero, `p₅ = H² g₁`, `q₉ = (5/3) g₁ H⁴`,
`9 q₈ = H² (5 H g₁² + 15 p₄ + κ H²)`, and the solved septic row
`81 q₇ = H (135 p₃ H + 90 p₄ g₁ - 5 H g₁³ + 12 κ g₁ H²)`. -/
theorem normalized610ScaleTwo_alignedThirdFace_nonsquareChamber_packet
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
    ∃ (κ : K) (g1 : K[X]),
      p.coeff 5 = H ^ 2 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 3 : K) * g1 * H ^ 4 ∧
        (9 : K[X]) * q.coeff 8 =
          H ^ 2 * ((5 : K[X]) * H * g1 ^ 2 + (15 : K[X]) * p.coeff 4 +
            Polynomial.C κ * H ^ 2) ∧
        (81 : K[X]) * q.coeff 7 =
          H * ((135 : K[X]) * p.coeff 3 * H +
            (90 : K[X]) * p.coeff 4 * g1 - (5 : K[X]) * H * g1 ^ 3 +
            Polynomial.C κ * ((12 : K[X]) * g1 * H ^ 2)) ∧
        alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = 0 := by
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
  refine ⟨κ, g1, ?_, ?_, ?_, hq7, hD0⟩
  · rw [hg, hg1]; ring
  · rw [hq9, hg, hg1]; ring
  · rw [hq8, hg1]; ring

/-- Honest square/nonsquare chamber split of the consumed degree-`12`
aligned row.  Neither chamber is excluded and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedThirdFace_chamberDichotomy
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
      ∃ (κ μ : K) (w : K[X]),
        p.coeff 5 = h0 ^ 3 * w ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * w * h0 ^ 7 ∧
          (9 : K[X]) * q.coeff 8 =
            h0 ^ 4 * ((5 : K[X]) * w ^ 2 + (15 : K[X]) * p.coeff 4 +
              Polynomial.C κ * h0 ^ 4) ∧
          (81 : K[X]) * q.coeff 7 =
            h0 * ((135 : K[X]) * p.coeff 3 * h0 ^ 3 +
              (90 : K[X]) * p.coeff 4 * w - (5 : K[X]) * w ^ 3 +
              Polynomial.C κ * ((12 : K[X]) * w * h0 ^ 4) -
              Polynomial.C μ * h0 ^ 6)) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g1 : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * g1 * H ^ 4 ∧
          (9 : K[X]) * q.coeff 8 =
            H ^ 2 * ((5 : K[X]) * H * g1 ^ 2 + (15 : K[X]) * p.coeff 4 +
              Polynomial.C κ * H ^ 2) ∧
          (81 : K[X]) * q.coeff 7 =
            H * ((135 : K[X]) * p.coeff 3 * H +
              (90 : K[X]) * p.coeff 4 * g1 - (5 : K[X]) * H * g1 ^ 3 +
              Polynomial.C κ * ((12 : K[X]) * g1 * H ^ 2))) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedThirdFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, w, hp5, hq9, hq8, hq7, _hD⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, w, hp5, hq9, hq8, hq7⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedThirdFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g1, hp5, hq9, hq8, hq7, _hD⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g1, hp5, hq9, hq8, hq7⟩

/-- Extended chamber-independent root jet of the consumed degree-`12`
row: at scale two the common core has a root, and the jet
`p₅, q₉, q₈, q₇` vanishes there. -/
theorem normalized610ScaleTwo_alignedThirdFace_rootJet
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
      (q.coeff 7).eval a = 0 := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  have hdi :=
    normalized610ScaleTwo_alignedThirdFace_chamberDichotomy
      hsource haligned
  dsimp only at hdi
  rcases hdi with
    ⟨h0, hh0, hHsq, κ, μ, w, hp5, hq9, hq8, hq7⟩ |
    ⟨hnsq, κ, g1, hp5, hq9, hq8, hq7⟩
  · have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (7 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
  · have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    refine ⟨a, hroot, ?_, ?_, ?_, ?_⟩
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun f : K[X] => f.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)

#print axioms alignedThirdCoefficientJacobianRow_610
#print axioms alignedThirdDefect_weightedDerivative_identity_610
#print axioms alignedThirdDefectRow_eq_zero_610
#print axioms alignedThirdDefectPowerRelation_610
#print axioms alignedSquareThird_sqrt_610
#print axioms alignedSquareThird_core_610
#print axioms alignedSquareThird_descent_610
#print axioms alignedNonsquareThird_defect_eq_zero_610
#print axioms alignedNonsquareThird_solved_610
#print axioms normalized610ScaleTwo_alignedThirdFace_packet
#print axioms normalized610ScaleTwo_alignedThirdFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedThirdFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedThirdFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedThirdFace_rootJet

end Max11DegreeRoutes
