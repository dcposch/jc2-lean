import Fable810ScaleTwoAlignedFaceScratch
import LowScale810ScaleTwoThirdFace

/-! # Second aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedFaceScratch` opened the aligned face `N = 0` of
the normalized scale-two `(8,10)` source and consumed the degree-`15`
Keller row: `q₉ = (5/4) p₇ H`, the weight-fourteen polynomial first
integral `M = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇² = κ H⁷`, and the honest
square/nonsquare chamber split.  This file consumes the next unused
aligned row, the degree-`14` Jacobian coefficient — the first row that
sees `p₅` and `q₇`.

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0` and
the consumed degree-`15` relation
`C = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇² - κ H⁷ = 0`, the degree-`14` row is
the weighted derivative of the cleared half-weight defect

`D = 160 p₅ H⁸ - 128 q₇ H⁷ + 40 p₆ p₇ H⁴ - 5 p₇³ + 4 κ p₇ H⁷`,

via the exact multiplier identity

`32 H⁴ · row₁₄[p₈ = H⁴, q₁₀ = H⁵] = (2 H D' - 21 D H')
  - 72 H⁴ p₆' N + 48 H⁴ p₆ N' + (8 H p₇' + 21 p₇ H') C - 7 H p₇ C'`.

On the aligned face every right-hand correction vanishes, so
`2 H D' = 21 D H'` and the squared weight-twenty-one first integral

`D² = κ₂ H²¹`

holds for a preserved constant `κ₂`.  The odd exponent splits honestly
on the chambers of the previous packet:

* square chamber `H = h₀²`, `p₇ = h₀³ g`: the integral has a polynomial
  square root `D = μ h₀²¹` with `μ² = κ₂`, and the cubic term of the
  peeled core forces exactly one further descent `g = h₀ g₁` at the
  root of the linear square core; hence `p₇ = h₀⁴ g₁`,
  `q₉ = (5/4) g₁ h₀⁶`, `32 q₈ = h₀² (5 g₁² + 40 p₆ + κ h₀⁶)` — in
  particular `h₀² ∣ q₈` — and the factored quotient row
  `5 g₁ (g₁² - 8 p₆) = h₀² (160 p₅ h₀² - 128 q₇ + 4 κ g₁ h₀⁴ - μ h₀⁷)`.
  Unlike the `(6,10)` third aligned row, the mate `40 p₆ g₁` of the
  cubic blocks any second unconditional descent: at the root of `h₀`
  the honest branch is `g₁ = 0 ∨ g₁² = 8 p₆`, and neither branch is
  excluded.  The constant `μ` is preserved, not cleared.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₂ = 0` and `D = 0` identically; with `p₇ = H² g₂`
  from the previous packet, peeling `H⁶` leaves the factored quotient
  row `5 g₂ (g₂² - 8 p₆) = H (160 p₅ H - 128 q₇ + 4 κ g₂ H²)`, with the
  same honest root branch `g₂ = 0 ∨ g₂² = 8 p₆` at each (simple) root
  of the core.  No further descent of `p₇` is claimed.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero` and
`dvd_of_eval_eq_zero_of_simple_natDegree_two` from the `(6,8)` aligned
architecture, `dvd_of_sq_dvd_sq_poly`, and
`linearPolynomial_dvd_of_eval_eq_zero_810` (all generic in the degree
pair).  The chamber-independent root jet extends to `q₈`: at a root of
the common core the coefficients `p₇, q₉, q₈` all vanish.  The septic
coefficient `q₇` is *not* killed at the root — the consumed row ties it
into the factored quotient instead.

No closure is claimed.  Both chambers remain open, the zero branches
(`g₁ = 0`, `g₂ = 0`, `κ = 0`, `κ₂ = 0`, `μ = 0`) and the quadratic root
branch `g² = 8 p₆` are not excluded, and the constants `κ`, `κ₂ = μ²`
are preserved where not forced.  No individual vanishing of `p₅`, `p₆`,
`q₇` is claimed.  The next unused Keller row on the aligned face is the
degree-`13` Jacobian coefficient, the first row that sees `p₄` and
`q₆`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`14` Keller coefficient on the aligned face -/

/-- The third row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`14` Jacobian coefficient, the first
aligned row that sees `p₅` and `q₇`. -/
theorem alignedThirdCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 7).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 6).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 5).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 7).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 8).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 9).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) *
          (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 14) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (14 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 14 :
      Finset (ℕ × ℕ)) =
      ({(0, 14), (1, 13), (2, 12), (3, 11), (4, 10), (5, 9), (6, 8),
        (7, 7), (8, 6), (9, 5), (10, 4), (11, 3), (12, 2), (13, 1),
        (14, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC7, hC8, hC9, hC10, hC6, hC5]
  linear_combination hcoeff

/-! ## Aligned third defect -/

/-- Cleared half-weight defect of the degree-`14` aligned `(8,10)` row:
`D = 160 p₅ H⁸ - 128 q₇ H⁷ + 40 p₆ p₇ H⁴ - 5 p₇³ + 4 κ p₇ H⁷`.  On the
aligned face its square is a polynomial first integral of weight
twenty-one. -/
def alignedThirdDefect810 {K : Type*} [CommRing K]
    (H a5 a6 a7 b7 : K[X]) (κ : K) : K[X] :=
  (160 : K[X]) * a5 * H ^ 8 - (128 : K[X]) * b7 * H ^ 7 +
    (40 : K[X]) * a6 * a7 * H ^ 4 - (5 : K[X]) * a7 ^ 3 +
    Polynomial.C κ * ((4 : K[X]) * a7 * H ^ 7)

set_option maxHeartbeats 256000000 in
/-- Exact combination of the degree-`14` Jacobian expression with the
weighted derivative of `D`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15` row. -/
theorem alignedThirdDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K] (H a5 a6 a7 b7 b8 b9 : K[X]) (κ : K) :
    (32 : K[X]) * H ^ 4 *
        ((H ^ 4).derivative * (b7 * (7 : K[X])) +
          a7.derivative * (b8 * (8 : K[X])) +
          a6.derivative * (b9 * (9 : K[X])) +
          a5.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b7.derivative +
          (a7 * (7 : K[X])) * b8.derivative +
          (a6 * (6 : K[X])) * b9.derivative +
          (a5 * (5 : K[X])) * (H ^ 5).derivative)) =
      ((2 : K[X]) * H *
          (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
        (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
          H.derivative) -
        (72 : K[X]) * H ^ 4 * a6.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (48 : K[X]) * H ^ 4 * a6 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((8 : K[X]) * H * a7.derivative +
            (21 : K[X]) * a7 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (7 : K[X]) * H * a7 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative := by
  simp only [alignedThirdDefect810, Polynomial.derivative_sub,
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

/-- On the aligned face, with the consumed degree-`15` integral, the
degree-`14` row is the weighted derivative `2 H D' - 21 D H' = 0`. -/
theorem alignedThirdDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 7) κ).derivative -
      (21 : K[X]) *
        alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedThirdCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC7, hC8, hC9, hC10, hC6, hC5] at hrow
  have hC0 :
      (32 : K[X]) * q.coeff 8 * H ^ 3 - (40 : K[X]) * p.coeff 6 * H ^ 4 -
          (5 : K[X]) * p.coeff 7 ^ 2 - Polynomial.C κ * H ^ 7 = 0 := by
    have hM' :
        (32 : K[X]) * q.coeff 8 * H ^ 3 -
            (40 : K[X]) * p.coeff 6 * H ^ 4 -
            (5 : K[X]) * p.coeff 7 ^ 2 = Polynomial.C κ * H ^ 7 := by
      simpa only [alignedSecondDefect810] using hM
    linear_combination hM'
  have hid := alignedThirdDefect_weightedDerivative_identity_810
    H (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 7) (q.coeff 8)
    (q.coeff 9) κ
  rw [hrow, haligned, hC0] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-twenty-one polynomial first integral of the aligned
`(8,10)` third defect: `D² = κ₂ H²¹`. -/
theorem alignedThirdDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₂ : K,
      alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
          (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₂ * H ^ 21 := by
  let D : K[X] :=
    alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
      (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * D.derivative -
        (21 : K[X]) * D * H.derivative = 0 := by
    simpa only [D] using
      alignedThirdDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC21 : Polynomial.C (21 : K) = (21 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 21) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (21 : K) * H ^ (21 - 1) * H.derivative) -
          Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative * H ^ 21 =
          D * H ^ 20 *
            (Polynomial.C (21 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by
        ring
      _ = 0 := by
        rw [hC21, hC2]
        have hfac :
            (21 : K[X]) * D * H.derivative -
              (2 : K[X]) * H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 21 hH) hW

/-! ## Root branch of the factored quotient -/

/-- Evaluating the factored quotient row at a root of its cofactor:
either the descent quotient vanishes there, or its square meets `8 p₆`.
Neither branch is excluded. -/
theorem alignedThird_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (5 : K[X]) * g * (g ^ 2 - (8 : K[X]) * a6) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨ g.eval a ^ 2 = 8 * a6.eval a := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h5g | hquad
  · exact Or.inl
      ((mul_eq_zero.mp h5g).resolve_left (by norm_num : (5 : K) ≠ 0))
  · exact Or.inr (by linear_combination hquad)

/-! ## Square chamber -/

/-- In the square chamber the weight-twenty-one integral has a
polynomial square root with square core: `D = μ h₀²¹` with `μ² = κ₂`.
The constant `μ` is preserved, not cleared. -/
theorem alignedSquareThird_sqrt_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a5 a6 a7 b7 : K[X]} {κ κ₂ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hD2 : alignedThirdDefect810 H a5 a6 a7 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 21) :
    ∃ μ : K, μ ^ 2 = κ₂ ∧
      alignedThirdDefect810 H a5 a6 a7 b7 κ =
        Polynomial.C μ * h0 ^ 21 := by
  set D : K[X] := alignedThirdDefect810 H a5 a6 a7 b7 κ with hDdef
  have hdvd : (h0 ^ 21) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C κ₂, ?_⟩
    rw [hD2, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C κ₂ := by
    have h42 := hD2
    rw [hF, hHsq] at h42
    apply mul_left_cancel₀ (pow_ne_zero 42 hh0)
    linear_combination h42
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
`h₀⁹` from `D = μ h₀²¹` on `p₇ = h₀³ g` leaves the degree-`12`
chamber core `E = μ h₀¹²`. -/
theorem alignedSquareThird_core_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g a5 a6 a7 b7 : K[X]} {κ μ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 3 * g)
    (hD : alignedThirdDefect810 H a5 a6 a7 b7 κ =
      Polynomial.C μ * h0 ^ 21) :
    (160 : K[X]) * a5 * h0 ^ 7 - (128 : K[X]) * b7 * h0 ^ 5 +
        (40 : K[X]) * a6 * g * h0 ^ 2 - (5 : K[X]) * g ^ 3 +
        Polynomial.C κ * ((4 : K[X]) * g * h0 ^ 8) =
      Polynomial.C μ * h0 ^ 12 := by
  have hD' :
      (160 : K[X]) * a5 * (h0 ^ 2) ^ 8 -
          (128 : K[X]) * b7 * (h0 ^ 2) ^ 7 +
          (40 : K[X]) * a6 * (h0 ^ 3 * g) * (h0 ^ 2) ^ 4 -
          (5 : K[X]) * (h0 ^ 3 * g) ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * (h0 ^ 3 * g) * (h0 ^ 2) ^ 7) =
        Polynomial.C μ * h0 ^ 21 := by
    simpa only [alignedThirdDefect810, hHsq, hg] using hD
  apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
  linear_combination hD'

/-- Single forced descent at the root of the linear square core: the
cubic term of the chamber core kills the quotient at the root, so
`h₀ ∣ g`, and the peeled relation solves `128 q₇ h₀²` and factors as
`5 g₁ (g₁² - 8 p₆) = h₀² (160 p₅ h₀² - 128 q₇ + 4 κ g₁ h₀⁴ - μ h₀⁷)`.
The mate `40 p₆ g₁` of the cubic blocks any second unconditional
descent. -/
theorem alignedSquareThird_descent_810 {K : Type*} [Field K] [CharZero K]
    {h0 g a5 a6 b7 : K[X]} {κ μ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hE : (160 : K[X]) * a5 * h0 ^ 7 - (128 : K[X]) * b7 * h0 ^ 5 +
        (40 : K[X]) * a6 * g * h0 ^ 2 - (5 : K[X]) * g ^ 3 +
        Polynomial.C κ * ((4 : K[X]) * g * h0 ^ 8) =
      Polynomial.C μ * h0 ^ 12) :
    ∃ g1 : K[X], g = h0 * g1 ∧
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9 ∧
      (5 : K[X]) * g1 * (g1 ^ 2 - (8 : K[X]) * a6) =
        h0 ^ 2 * ((160 : K[X]) * a5 * h0 ^ 2 - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 4) -
          Polynomial.C μ * h0 ^ 7) := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hg3 : (5 : K[X]) * g ^ 3 =
      h0 * ((160 : K[X]) * a5 * h0 ^ 6 - (128 : K[X]) * b7 * h0 ^ 4 +
        (40 : K[X]) * a6 * g * h0 +
        Polynomial.C κ * ((4 : K[X]) * g * h0 ^ 7) -
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
  have hcore : (128 : K[X]) * b7 * h0 ^ 2 =
      (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
        (5 : K[X]) * g1 ^ 3 +
        Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
        Polynomial.C μ * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    rw [hg1] at hE
    linear_combination -hE
  exact ⟨g1, hg1, hcore, by linear_combination hcore⟩

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the weight-twenty-one
integral forces its constant to vanish, and with it the whole third
defect. -/
theorem alignedNonsquareThird_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a5 a6 a7 b7 : k[X]} {κ κ₂ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hD2 : alignedThirdDefect810 H a5 a6 a7 b7 κ ^ 2 =
      Polynomial.C κ₂ * H ^ 21) :
    κ₂ = 0 ∧ alignedThirdDefect810 H a5 a6 a7 b7 κ = 0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set D : k[X] := alignedThirdDefect810 H a5 a6 a7 b7 κ with hDdef
  have hdvd : (H ^ 10) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C κ₂ * H, ?_⟩
    rw [hD2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₂ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hH)
    have h20 := hD2
    rw [hG] at h20
    linear_combination h20
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

/-- Peeling `H⁶` from the vanished third defect on `p₇ = H² g₂`: the
degree-`14` row survives as the factored quotient
`5 g₂ (g₂² - 8 p₆) = H (160 p₅ H - 128 q₇ + 4 κ g₂ H²)`.  No further
descent of `p₇` is claimed: the mate `40 p₆ g₂` of the cubic blocks
it. -/
theorem alignedNonsquareThird_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a5 a6 a7 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hD0 : alignedThirdDefect810 H a5 a6 a7 b7 κ = 0) :
    (160 : K[X]) * a5 * H ^ 2 - (128 : K[X]) * b7 * H +
        (40 : K[X]) * a6 * g2 - (5 : K[X]) * g2 ^ 3 +
        Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 3) = 0 ∧
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2)) := by
  have hD0' :
      (160 : K[X]) * a5 * H ^ 8 - (128 : K[X]) * b7 * H ^ 7 +
          (40 : K[X]) * a6 * (H ^ 2 * g2) * H ^ 4 -
          (5 : K[X]) * (H ^ 2 * g2) ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * (H ^ 2 * g2) * H ^ 7) = 0 := by
    simpa only [alignedThirdDefect810, hg2] using hD0
  have hpeel :
      (160 : K[X]) * a5 * H ^ 2 - (128 : K[X]) * b7 * H +
          (40 : K[X]) * a6 * g2 - (5 : K[X]) * g2 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 3) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hH)
    rw [mul_zero]
    linear_combination hD0'
  exact ⟨hpeel, by linear_combination -hpeel⟩

/-! ## Source-facing third-row packets -/

/-- Source-facing squared weight-twenty-one integral of a normalized
aligned scale-two `(8,10)` source: the degree-`14` row is consumed into
`D² = κ₂ H²¹` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedThirdFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₂ * H ^ 21 := by
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
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  exact ⟨κ, κ₂, aligned_q9_solved_810 haligned, hM, hD2⟩

/-- Exact square-chamber third packet of a normalized aligned scale-two
`(8,10)` source: `p₇ = h₀⁴ g₁`, `q₉ = (5/4) g₁ h₀⁶`,
`32 q₈ = h₀² (5 g₁² + 40 p₆ + κ h₀⁶)`, the factored quotient row
`5 g₁ (g₁² - 8 p₆) = h₀² (160 p₅ h₀² - 128 q₇ + 4 κ g₁ h₀⁴ - μ h₀⁷)`
with its honest root branch, and the square root `D = μ h₀²¹` of the
weight-twenty-one integral. -/
theorem normalized810ScaleTwo_alignedThirdFace_squareChamber_packet
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
    ∃ (κ μ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        (32 : K[X]) * q.coeff 8 =
          h0 ^ 2 * ((5 : K[X]) * g1 ^ 2 + (40 : K[X]) * p.coeff 6 +
            Polynomial.C κ * h0 ^ 6) ∧
        (5 : K[X]) * g1 * (g1 ^ 2 - (8 : K[X]) * p.coeff 6) =
          h0 ^ 2 * ((160 : K[X]) * p.coeff 5 * h0 ^ 2 -
            (128 : K[X]) * q.coeff 7 +
            Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 4) -
            Polynomial.C μ * h0 ^ 7) ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∨ g1.eval a ^ 2 = 8 * (p.coeff 6).eval a) ∧
        alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 21 := by
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
  have hE := alignedSquareThird_core_810 hh0 hHsq hg hD
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨g1, hg1, _hcore, hfac⟩ :=
    alignedSquareThird_descent_810 hh0 hdeg1 hE
  have hbranch : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∨ g1.eval a ^ 2 = 8 * (p.coeff 6).eval a := by
    intro a ha
    refine alignedThird_factored_rootBranch_810 hfac ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, ha,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  refine ⟨κ, μ, g1, ?_, ?_, ?_, hfac, hbranch, hD⟩
  · rw [hg, hg1]; ring
  · rw [hq9, hg, hg1, hHsq]; ring
  · rw [hq8, hg1]; ring

/-- Exact nonsquare-chamber third packet of a normalized aligned
scale-two `(8,10)` source: the weight-twenty-one constant vanishes, the
third defect is identically zero, `p₇ = H² g₂`, `q₉ = (5/4) g₂ H³`,
`32 q₈ = H (5 g₂² + 40 p₆ + κ H³)`, and the factored quotient row
`5 g₂ (g₂² - 8 p₆) = H (160 p₅ H - 128 q₇ + 4 κ g₂ H²)` with its honest
root branch. -/
theorem normalized810ScaleTwo_alignedThirdFace_nonsquareChamber_packet
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
        (32 : K[X]) * q.coeff 8 =
          H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * p.coeff 6 +
            Polynomial.C κ * H ^ 3) ∧
        (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * p.coeff 6) =
          H * ((160 : K[X]) * p.coeff 5 * H - (128 : K[X]) * q.coeff 7 +
            Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2)) ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∨ g2.eval a ^ 2 = 8 * (p.coeff 6).eval a) ∧
        alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ = 0 := by
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
  refine ⟨κ, g2, hg2, ?_, hq8, hfac, hbranch, hD0⟩
  rw [hq9, hg2]
  ring

/-- Honest square/nonsquare chamber split of the consumed degree-`14`
aligned row.  Neither chamber is excluded, neither root branch of the
factored quotient is excluded, and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedThirdFace_chamberDichotomy
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
      ∃ (κ μ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (32 : K[X]) * q.coeff 8 =
            h0 ^ 2 * ((5 : K[X]) * g1 ^ 2 + (40 : K[X]) * p.coeff 6 +
              Polynomial.C κ * h0 ^ 6) ∧
          (5 : K[X]) * g1 * (g1 ^ 2 - (8 : K[X]) * p.coeff 6) =
            h0 ^ 2 * ((160 : K[X]) * p.coeff 5 * h0 ^ 2 -
              (128 : K[X]) * q.coeff 7 +
              Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 4) -
              Polynomial.C μ * h0 ^ 7) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∨ g1.eval a ^ 2 = 8 * (p.coeff 6).eval a)) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (32 : K[X]) * q.coeff 8 =
            H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * p.coeff 6 +
              Polynomial.C κ * H ^ 3) ∧
          (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * p.coeff 6) =
            H * ((160 : K[X]) * p.coeff 5 * H -
              (128 : K[X]) * q.coeff 7 +
              Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2)) ∧
          (∀ a : K, H.eval a = 0 →
            g2.eval a = 0 ∨ g2.eval a ^ 2 = 8 * (p.coeff 6).eval a)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized810ScaleTwo_alignedThirdFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, g1, hp7, hq9, hq8, hfac, hbranch, _hD⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, g1, hp7, hq9, hq8, hfac, hbranch⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedThirdFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, hq8, hfac, hbranch, _hD⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g2, hp7, hq9, hq8, hfac, hbranch⟩

/-- Extended chamber-independent root jet of the consumed degree-`14`
row: at scale two the common core has a root, and the jet `p₇, q₉, q₈`
vanishes there.  The septic coefficient `q₇` is *not* claimed to vanish
— the consumed row ties it into the factored quotient instead. -/
theorem normalized810ScaleTwo_alignedThirdFace_rootJet
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
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  have hdi :=
    normalized810ScaleTwo_alignedThirdFace_chamberDichotomy
      hsource haligned
  dsimp only at hdi
  rcases hdi with
    ⟨h0, hh0, hHsq, κ, μ, g1, hp7, hq9, hq8, _hfac, _hbranch⟩ |
    ⟨hnsq, κ, g2, hp7, hq9, hq8, _hfac, _hbranch⟩
  · have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp7, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (6 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (32 : K) ≠ 0)
  · have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    refine ⟨a, hroot, ?_, ?_, ?_⟩
    · rw [hp7, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun f : K[X] => f.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (32 : K) ≠ 0)

#print axioms alignedThirdCoefficientJacobianRow_810
#print axioms alignedThirdDefect_weightedDerivative_identity_810
#print axioms alignedThirdDefectRow_eq_zero_810
#print axioms alignedThirdDefectPowerRelation_810
#print axioms alignedThird_factored_rootBranch_810
#print axioms alignedSquareThird_sqrt_810
#print axioms alignedSquareThird_core_810
#print axioms alignedSquareThird_descent_810
#print axioms alignedNonsquareThird_defect_eq_zero_810
#print axioms alignedNonsquareThird_solved_810
#print axioms normalized810ScaleTwo_alignedThirdFace_packet
#print axioms normalized810ScaleTwo_alignedThirdFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedThirdFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedThirdFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedThirdFace_rootJet

end Max11DegreeRoutes
