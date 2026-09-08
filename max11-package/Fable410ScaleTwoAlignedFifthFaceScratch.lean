import Fable410ScaleTwoAlignedFourthFaceScratch

/-! # Fifth aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedFourthFaceScratch` consumed the degree-`8`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`15/2` first integral `M₆² = κ₄ H¹⁵` of the fifth defect and the
solved quintic coefficient `q₅` in both chambers.  This file consumes
the next unused aligned row, the degree-`7` Jacobian coefficient — the
first row that sees `q₄` — derived here directly from the literal
Keller bracket.

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10`, degree-`9`, and degree-`8` brackets of `M₂`,
`M₄`, and `M₆`, the degree-`7` row is the weighted derivative of the
cleared sixth defect

`M₈ = 7680 p₀ p₂ H⁸ - 2048 q₄ H⁷ + 1920 p₀ p₃² H⁶ + 3840 p₁² H⁸
  + 3840 p₁ p₂ p₃ H⁶ - 320 p₁ p₃³ H⁴ + 640 p₂³ H⁶ - 480 p₂² p₃² H⁴
  + 120 p₂ p₃⁴ H² - 10 p₃⁶
  + κ (512 p₀ H⁹ + 512 p₁ p₃ H⁷ + 256 p₂² H⁷)
  - 5 p₃ M₆ - (6 p₃² + 24 p₂ H²) M₄
  - (224 p₁ H⁴ + 168 p₂ p₃ H² - 7 p₃³) M₂`,

kept in factored form through the previous defects, via the exact
multiplier identity

`512 H⁶ · row₇[p₄ = H²] = (H M₈' - 9 M₈ H')
  + 4 p₃ (2 H M₆' - 15 M₆ H')
  + (32 p₂ H² + 24 p₃²) (H M₄' - 6 M₄ H')
  + (28 p₃³ + 224 p₂ p₃ H² + 128 p₁ H⁴) (2 H M₂' - 9 M₂ H')
  + 512 H⁶ p₀' R`.

The correction module carries NO aligned-face residual `N` at all: the
only correction beyond the consumed brackets is the single term
`512 H⁶ p₀' R`.  On the aligned face every right-hand correction
vanishes, so `H M₈' = 9 M₈ H'` and the weight-`9` polynomial first
integral

`M₈ = κ₅ H⁹`

holds for a preserved constant `κ₅` — an even-type first-order
integral like `M₄ = κ₃ H⁶`, chamber-free, with no square-root
extraction and hence no parity split.  The chambers then specialize the
consumed row honestly, and the `h`-adic core is a PERFECT CUBE:

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`: cancelling `h₀¹²` exposes the
  `h₀`-free core `-10 (u² - 4 p₂)³`, so `h₀² ∣ (u² - 4 p₂)³` and the
  linear descent forces the NEW divisibility `u² - 4 p₂ = h₀ v` — the
  first aligned constraint that pins `p₂` against the chamber quotient
  `u` modulo the half-core.  One more cancellation then solves the
  quartic-row letter outright:
  `2048 q₄ = 3840 p₁ p₂ u - 320 p₁ u³ + 256 κ p₂²
  + h₀ (μ (7 u³ - 168 p₂ u) - 10 v³)
  + h₀² (7680 p₀ p₂ + 1920 p₀ u² + 3840 p₁² + 512 κ p₁ u
  - κ₃ (6 u² + 24 p₂)) - h₀³ (224 μ p₁ + 5 μ₂ u)
  + h₀⁴ (512 κ p₀ - κ₅)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`, `M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`:
  cancelling `H⁶` exposes the same cube `-10 (g² - 4 p₂)³`, the
  simple-root descent forces `g² - 4 p₂ = H f`, and the row solves
  `2048 q₄ = 3840 p₁ p₂ g - 320 p₁ g³ + 256 κ p₂²
  + H (7680 p₀ p₂ + 1920 p₀ g² + 3840 p₁² + 512 κ p₁ g
  - κ₃ (6 g² + 24 p₂)) + H² (512 κ p₀ - κ₅ - 10 f³)`.

The honest new root content, chamber-uniform in the quotient `w`
(`u` or `g`): the QUADRATIC root kill `w(a)² = 4 p₂(a)` — the cube of
the deg-`8` face's quintic family collapses to a closed constraint
between the chamber quotient and `p₂` at the core root — and the value
ties `2048 q₄(a) = 3840 p₁ p₂ w - 320 p₁ w³ + 256 κ p₂²` at `a`,
simplifying on the kill to `128 q₄(a) = 40 p₁(a) w(a)³ + κ w(a)⁴`.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two` and
`nonsquare_natDegree_two_derivative_ne_zero` (tracked `(6,8)` aligned
architecture), `natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, and the previous faces' chamber quotients.  The
weight-`9` Wronskian quotient `ninthPowerRelation_of_weightNineRow_410`
is new but generic.

No closure is claimed.  Both chambers remain open, the zero branches
(`u = 0`, `g = 0`, `v = 0`, `f = 0`, `μ = 0`, `μ₂ = 0`, `κ = 0`,
`κ₂ = 0`, `κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`) are not excluded, and the
constants are preserved where not previously forced.  `p₀, p₁, p₂` are
constrained only through the solved forms and the new divisibility.
The next unused Keller row on the aligned face is the degree-`6`
Jacobian coefficient, the first row that sees `q₃`.  No total-degree or
twice-prime theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`7` Keller coefficient on the aligned face -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`7` Jacobian coefficient, the first
aligned row that sees `q₄`.  It is derived directly from the Keller
bracket. -/
theorem alignedSixthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
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
        (7, 0)} :
        Finset (ℕ × ℕ)) := by decide
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
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC4, hC5, hC6, hC7, hC8, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned sixth defect -/

/-- Cleared sixth defect of the degree-`7` aligned `(4,10)` row, kept in
factored form through the third defect `M₂`, the fourth defect `M₄`,
and the fifth defect `M₆`:
`M₈ = 7680 p₀ p₂ H⁸ - 2048 q₄ H⁷ + 1920 p₀ p₃² H⁶ + 3840 p₁² H⁸
+ 3840 p₁ p₂ p₃ H⁶ - 320 p₁ p₃³ H⁴ + 640 p₂³ H⁶ - 480 p₂² p₃² H⁴
+ 120 p₂ p₃⁴ H² - 10 p₃⁶ + κ (512 p₀ H⁹ + 512 p₁ p₃ H⁷ + 256 p₂² H⁷)
- 5 p₃ M₆ - (6 p₃² + 24 p₂ H²) M₄
- (224 p₁ H⁴ + 168 p₂ p₃ H² - 7 p₃³) M₂`.  Every monomial has exact
`H`-weight `9`; on the aligned face it is a polynomial first integral
of the even-type ninth-power shape. -/
def alignedSixthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (7680 : K[X]) * a0 * a2 * H ^ 8 - (2048 : K[X]) * b4 * H ^ 7 +
    (1920 : K[X]) * a0 * a3 ^ 2 * H ^ 6 +
    (3840 : K[X]) * a1 ^ 2 * H ^ 8 +
    (3840 : K[X]) * a1 * a2 * a3 * H ^ 6 -
    (320 : K[X]) * a1 * a3 ^ 3 * H ^ 4 +
    (640 : K[X]) * a2 ^ 3 * H ^ 6 -
    (480 : K[X]) * a2 ^ 2 * a3 ^ 2 * H ^ 4 +
    (120 : K[X]) * a2 * a3 ^ 4 * H ^ 2 - (10 : K[X]) * a3 ^ 6 +
    Polynomial.C κ *
      ((512 : K[X]) * a0 * H ^ 9 + (512 : K[X]) * a1 * a3 * H ^ 7 +
        (256 : K[X]) * a2 ^ 2 * H ^ 7) -
    (5 : K[X]) * a3 * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((6 : K[X]) * a3 ^ 2 + (24 : K[X]) * a2 * H ^ 2) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((224 : K[X]) * a1 * H ^ 4 + (168 : K[X]) * a2 * a3 * H ^ 2 -
      (7 : K[X]) * a3 ^ 3) * alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`7` Jacobian expression with the
weight-`9` bracket of `M₈`.  The corrections are the consumed
degree-`10`, degree-`9`, and degree-`8` brackets of `M₂`, `M₄`, and
`M₆`, and a single term against the consumed degree-`11` relation
`R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴`; the aligned-face residual `N`
does not appear at all.  Every correction vanishes on the aligned
face. -/
theorem alignedSixthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b4 b5 b6 b7 b8 : K[X]) (κ : K) :
    (512 : K[X]) * H ^ 6 *
        ((H ^ 2).derivative * (b4 * (4 : K[X])) +
          a3.derivative * (b5 * (5 : K[X])) +
          a2.derivative * (b6 * (6 : K[X])) +
          a1.derivative * (b7 * (7 : K[X])) +
          a0.derivative * (b8 * (8 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b4.derivative +
          (a3 * (3 : K[X])) * b5.derivative +
          (a2 * (2 : K[X])) * b6.derivative +
          a1 * b7.derivative)) =
      (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ).derivative -
        (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
          H.derivative) +
        (4 : K[X]) * a3 *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((32 : K[X]) * a2 * H ^ 2 + (24 : K[X]) * a3 ^ 2) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((28 : K[X]) * a3 ^ 3 + (224 : K[X]) * a2 * a3 * H ^ 2 +
            (128 : K[X]) * a1 * H ^ 4) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) +
        (512 : K[X]) * H ^ 6 * a0.derivative *
          ((8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
            (15 : K[X]) * a3 ^ 2 * H - Polynomial.C κ * H ^ 4) := by
  simp only [alignedSixthDefect410, alignedFifthDefect410,
    alignedFourthDefect410, alignedThirdDefect410,
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

/-- On the aligned face, with the consumed degree-`11` through
degree-`8` rows, the degree-`7` row is the weighted derivative
`H M₈' - 9 M₈ H' = 0`. -/
theorem alignedSixthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
          κ).derivative -
      (9 : K[X]) *
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedSixthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC4, hC5, hC6, hC7, hC8, hC3, hC2] at hrow
  have hR :
      (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
          (15 : K[X]) * p.coeff 3 ^ 2 * H - Polynomial.C κ * H ^ 4 =
        0 := by
    have hM' :
        (8 : K[X]) * q.coeff 8 - (20 : K[X]) * p.coeff 2 * H ^ 3 -
            (15 : K[X]) * p.coeff 3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
      simpa only [alignedSecondDefect410] using hM
    linear_combination hM'
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedSixthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 4)
    (q.coeff 5) (q.coeff 6) (q.coeff 7) (q.coeff 8) κ
  rw [hrow, hR, hB2, hB4, hB6] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-nine polynomial first integral -/

/-- Generic Wronskian quotient for the weight-nine bracket: over a
characteristic-zero field, `H D' - 9 D H' = 0` forces `D = C c * H⁹`.
The bracket is first-order, so the integral needs no square root of
`H` and no parity split. -/
theorem ninthPowerRelation_of_weightNineRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (9 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 9 := by
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hW : Polynomial.wronskian D (H ^ 9) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (9 : K) * H ^ (9 - 1) * H.derivative) -
          D.derivative * H ^ 9 =
          H ^ 8 *
            (Polynomial.C (9 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC9]
        have hfac :
            (9 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 9 hH) hW

/-- Weight-nine polynomial first integral of the aligned `(4,10)` sixth
defect: `M₈ = κ₅ H⁹` — even-type and chamber-free, one level below the
odd fifteenth-power shape of the degree-`8` row. -/
theorem alignedSixthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₅ : K,
      alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₅ * H ^ 9 :=
  ninthPowerRelation_of_weightNineRow_410 hH
    (alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

/-- Cleared square-core form of the sixth defect relation: cancelling
`h₀¹²` from `M₈ = κ₅ h₀¹⁸` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵` exposes the `h₀`-free core
`-10 (u² - 4 p₂)³` — a perfect cube of the quadratic discriminator
`u² - 4 p₂` — carried by `h₀²` against the explicit quotient. -/
theorem alignedSquareSixth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b4 b5 b6 b7 : K[X]} {κ μ κ₃ μ₂ κ₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9) :
    (10 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 =
      h0 ^ 2 *
        ((3840 : K[X]) * a1 * a2 * u - (320 : K[X]) * a1 * u ^ 3 +
          Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) -
          (2048 : K[X]) * b4 +
          h0 * (Polynomial.C μ *
            ((7 : K[X]) * u ^ 3 - (168 : K[X]) * a2 * u)) +
          h0 ^ 2 * ((7680 : K[X]) * a0 * a2 +
            (1920 : K[X]) * a0 * u ^ 2 + (3840 : K[X]) * a1 ^ 2 +
            Polynomial.C κ * ((512 : K[X]) * a1 * u) -
            Polynomial.C κ₃ *
              ((6 : K[X]) * u ^ 2 + (24 : K[X]) * a2)) -
          h0 ^ 3 * (Polynomial.C μ * ((224 : K[X]) * a1) +
            Polynomial.C μ₂ * ((5 : K[X]) * u)) +
          h0 ^ 4 * (Polynomial.C κ * ((512 : K[X]) * a0) -
            Polynomial.C κ₅)) := by
  have hM8' := hM8
  simp only [alignedSixthDefect410] at hM8'
  rw [hM2, hM4, hM6, hHsq, hp3] at hM8'
  apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
  linear_combination -hM8'

/-- The consumed degree-`7` row in the square chamber: the `h₀`-free
part of the chamber core is the perfect cube `-10 (u² - 4 p₂)³`, so the
linear descent forces the NEW divisibility `u² - 4 p₂ = h₀ v` — the
first aligned row that constrains `p₂` against the chamber quotient —
and cancelling `h₀²` solves the quartic row against the preserved
constants `μ`, `κ₃`, `μ₂`, and `κ₅`.  The new letter `q₄` carries no
`h₀` factor. -/
theorem alignedSquareSixth_descent_410 {K : Type*} [Field K] [CharZero K]
    {h0 u a0 a1 a2 b4 : K[X]} {κ μ κ₃ μ₂ κ₅ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1)
    (hcore :
      (10 : K[X]) * (u ^ 2 - (4 : K[X]) * a2) ^ 3 =
        h0 ^ 2 *
          ((3840 : K[X]) * a1 * a2 * u - (320 : K[X]) * a1 * u ^ 3 +
            Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) -
            (2048 : K[X]) * b4 +
            h0 * (Polynomial.C μ *
              ((7 : K[X]) * u ^ 3 - (168 : K[X]) * a2 * u)) +
            h0 ^ 2 * ((7680 : K[X]) * a0 * a2 +
              (1920 : K[X]) * a0 * u ^ 2 + (3840 : K[X]) * a1 ^ 2 +
              Polynomial.C κ * ((512 : K[X]) * a1 * u) -
              Polynomial.C κ₃ *
                ((6 : K[X]) * u ^ 2 + (24 : K[X]) * a2)) -
            h0 ^ 3 * (Polynomial.C μ * ((224 : K[X]) * a1) +
              Polynomial.C μ₂ * ((5 : K[X]) * u)) +
            h0 ^ 4 * (Polynomial.C κ * ((512 : K[X]) * a0) -
              Polynomial.C κ₅))) :
    ∃ v : K[X], u ^ 2 - (4 : K[X]) * a2 = h0 * v ∧
      (2048 : K[X]) * b4 =
        (3840 : K[X]) * a1 * a2 * u - (320 : K[X]) * a1 * u ^ 3 +
          Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) +
          h0 * (Polynomial.C μ *
            ((7 : K[X]) * u ^ 3 - (168 : K[X]) * a2 * u) -
            (10 : K[X]) * v ^ 3) +
          h0 ^ 2 * ((7680 : K[X]) * a0 * a2 +
            (1920 : K[X]) * a0 * u ^ 2 + (3840 : K[X]) * a1 ^ 2 +
            Polynomial.C κ * ((512 : K[X]) * a1 * u) -
            Polynomial.C κ₃ *
              ((6 : K[X]) * u ^ 2 + (24 : K[X]) * a2)) -
          h0 ^ 3 * (Polynomial.C μ * ((224 : K[X]) * a1) +
            Polynomial.C μ₂ * ((5 : K[X]) * u)) +
          h0 ^ 4 * (Polynomial.C κ * ((512 : K[X]) * a0) -
            Polynomial.C κ₅) := by
  have hkill : ∀ a : K, h0.eval a = 0 →
      (u ^ 2 - (4 : K[X]) * a2).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hcore
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [ha, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (10 : K) ≠ 0))
  obtain ⟨v, hv⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill
  refine ⟨v, hv, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
  rw [hv] at hcore
  linear_combination hcore

/-! ## Nonsquare chamber -/

/-- Cleared nonsquare-core form of the sixth defect relation:
cancelling `H⁶` from `M₈ = κ₅ H⁹` on `p₃ = H g`, `M₂ = 0`,
`M₄ = κ₃ H⁶`, `M₆ = 0` exposes the same perfect cube
`-10 (g² - 4 p₂)³` carried by a single `H` against the explicit
quotient. -/
theorem alignedNonsquareSixth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9) :
    (10 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 =
      H * ((3840 : K[X]) * a1 * a2 * g - (320 : K[X]) * a1 * g ^ 3 +
          Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) -
          (2048 : K[X]) * b4 +
          H * ((7680 : K[X]) * a0 * a2 + (1920 : K[X]) * a0 * g ^ 2 +
            (3840 : K[X]) * a1 ^ 2 +
            Polynomial.C κ * ((512 : K[X]) * a1 * g) -
            Polynomial.C κ₃ *
              ((6 : K[X]) * g ^ 2 + (24 : K[X]) * a2)) +
          H ^ 2 * (Polynomial.C κ * ((512 : K[X]) * a0) -
            Polynomial.C κ₅)) := by
  have hM8' := hM8
  simp only [alignedSixthDefect410] at hM8'
  rw [hM20, hM4, hM60, hg] at hM8'
  apply mul_left_cancel₀ (pow_ne_zero 6 hH)
  linear_combination -hM8'

/-- The consumed degree-`7` row in the nonsquare chamber: the cube
`10 (g² - 4 p₂)³` vanishes at both simple roots of `H`, so the
simple-root descent forces the NEW divisibility `g² - 4 p₂ = H f`, and
cancelling `H` solves the quartic row outright.  `q₄` carries no `H`
factor. -/
theorem alignedNonsquareSixth_descent_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H g a0 a1 a2 b4 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hcore :
      (10 : K[X]) * (g ^ 2 - (4 : K[X]) * a2) ^ 3 =
        H * ((3840 : K[X]) * a1 * a2 * g - (320 : K[X]) * a1 * g ^ 3 +
            Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) -
            (2048 : K[X]) * b4 +
            H * ((7680 : K[X]) * a0 * a2 +
              (1920 : K[X]) * a0 * g ^ 2 + (3840 : K[X]) * a1 ^ 2 +
              Polynomial.C κ * ((512 : K[X]) * a1 * g) -
              Polynomial.C κ₃ *
                ((6 : K[X]) * g ^ 2 + (24 : K[X]) * a2)) +
            H ^ 2 * (Polynomial.C κ * ((512 : K[X]) * a0) -
              Polynomial.C κ₅))) :
    ∃ f : K[X], g ^ 2 - (4 : K[X]) * a2 = H * f ∧
      (2048 : K[X]) * b4 =
        (3840 : K[X]) * a1 * a2 * g - (320 : K[X]) * a1 * g ^ 3 +
          Polynomial.C κ * ((256 : K[X]) * a2 ^ 2) +
          H * ((7680 : K[X]) * a0 * a2 + (1920 : K[X]) * a0 * g ^ 2 +
            (3840 : K[X]) * a1 ^ 2 +
            Polynomial.C κ * ((512 : K[X]) * a1 * g) -
            Polynomial.C κ₃ *
              ((6 : K[X]) * g ^ 2 + (24 : K[X]) * a2)) +
          H ^ 2 * (Polynomial.C κ * ((512 : K[X]) * a0) -
            Polynomial.C κ₅ - (10 : K[X]) * f ^ 3) := by
  have hkill : ∀ a : K, H.eval a = 0 →
      (g ^ 2 - (4 : K[X]) * a2).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hcore
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat] at hev
    rw [ha, zero_mul] at hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp hev).resolve_left (by norm_num : (10 : K) ≠ 0))
  obtain ⟨f, hf⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkill
  refine ⟨f, hf, ?_⟩
  apply mul_left_cancel₀ hH
  rw [hf] at hcore
  linear_combination hcore

/-! ## Source-facing sixth-row packets -/

/-- Source-facing weight-`9` integral of a normalized aligned scale-two
`(4,10)` source: the degree-`7` row is consumed into `M₈ = κ₅ H⁹` on
top of the previous aligned packet, together with the chamber-free root
jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedSixthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ : K,
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
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
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
  obtain ⟨κ₄, hM6⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₅, hM8⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber sixth packet of a normalized aligned scale-two
`(4,10)` source: the identifying chamber data, the weight-`9` form
`M₈ = κ₅ H⁹`, the NEW divisibility `u² - 4 p₂ = h₀ v`, and the solved
quartic row.  The constants `μ`, `κ₃`, `μ₂`, and `κ₅` are preserved,
not cleared, and `q₄` carries no `h₀` factor. -/
theorem normalized410ScaleTwo_alignedSixthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ : K) (u v : K[X]),
      p.coeff 3 = h0 ^ 2 * u ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C μ₂ * h0 ^ 15 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (2048 : K[X]) * q.coeff 4 =
          (3840 : K[X]) * p.coeff 1 * p.coeff 2 * u -
            (320 : K[X]) * p.coeff 1 * u ^ 3 +
            Polynomial.C κ * ((256 : K[X]) * p.coeff 2 ^ 2) +
            h0 * (Polynomial.C μ *
              ((7 : K[X]) * u ^ 3 - (168 : K[X]) * p.coeff 2 * u) -
              (10 : K[X]) * v ^ 3) +
            h0 ^ 2 * ((7680 : K[X]) * p.coeff 0 * p.coeff 2 +
              (1920 : K[X]) * p.coeff 0 * u ^ 2 +
              (3840 : K[X]) * p.coeff 1 ^ 2 +
              Polynomial.C κ * ((512 : K[X]) * p.coeff 1 * u) -
              Polynomial.C κ₃ *
                ((6 : K[X]) * u ^ 2 + (24 : K[X]) * p.coeff 2)) -
            h0 ^ 3 * (Polynomial.C μ * ((224 : K[X]) * p.coeff 1) +
              Polynomial.C μ₂ * ((5 : K[X]) * u)) +
            h0 ^ 4 * (Polynomial.C κ * ((512 : K[X]) * p.coeff 0) -
              Polynomial.C κ₅) := by
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
  obtain ⟨u, hu, _hq6⟩ := alignedSquareFourth_descent_410 hh0 hdeg1 hcore
  have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
    fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
  obtain ⟨v, hv, hq4⟩ := alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
  exact ⟨κ, μ, κ₃, μ₂, κ₅, u, v, hp3, hDform, hM4, hM6form, hM8form,
    hv, hq4⟩

/-- Exact nonsquare-chamber sixth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
weight-`9` form `M₈ = κ₅ H⁹`, the NEW divisibility `g² - 4 p₂ = H f`,
and the solved quartic row.  No parity kill occurs at this row — `κ₅`
is preserved in both chambers — and `q₄` carries no `H` factor. -/
theorem normalized410ScaleTwo_alignedSixthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ : K) (g f : K[X]),
      p.coeff 3 = H * g ∧
        alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (q.coeff 7) κ = 0 ∧
        alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 6 ∧
        alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = Polynomial.C κ₅ * H ^ 9 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        (2048 : K[X]) * q.coeff 4 =
          (3840 : K[X]) * p.coeff 1 * p.coeff 2 * g -
            (320 : K[X]) * p.coeff 1 * g ^ 3 +
            Polynomial.C κ * ((256 : K[X]) * p.coeff 2 ^ 2) +
            H * ((7680 : K[X]) * p.coeff 0 * p.coeff 2 +
              (1920 : K[X]) * p.coeff 0 * g ^ 2 +
              (3840 : K[X]) * p.coeff 1 ^ 2 +
              Polynomial.C κ * ((512 : K[X]) * p.coeff 1 * g) -
              Polynomial.C κ₃ *
                ((6 : K[X]) * g ^ 2 + (24 : K[X]) * p.coeff 2)) +
            H ^ 2 * (Polynomial.C κ * ((512 : K[X]) * p.coeff 0) -
              Polynomial.C κ₅ - (10 : K[X]) * f ^ 3) := by
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
  obtain ⟨κ₄, hM6rel⟩ :=
    alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₄, hM60⟩ :=
    fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
  obtain ⟨κ₅, hM8form⟩ :=
    alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore6 :=
    alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
  obtain ⟨f, hf, hq4⟩ :=
    alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
  exact ⟨κ, κ₃, κ₅, g, f, hg, hD0, hM4, hM60, hM8form, hf, hq4⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`7`
aligned row.  Both chambers carry the same perfect-cube core: the
quadratic discriminator `w² - 4 p₂` of the chamber quotient `w` is
divisible by the core (`h₀` resp. `H`), and the quartic-row letter `q₄`
is solved.  Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedSixthRow_chamberDichotomy
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
      ∃ (κ κ₅ : K) (u v : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 9 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₅ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
              (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 9 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedSixthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, u, v, hp3, _hM2f, _hM4, _hM6f, hM8,
      hv, _hq4⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, κ₅, u, v, hp3, hM8, hv⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedSixthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, g, f, hg, _hM20, _hM4, _hM60, hM8, hf,
      _hq4⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₅, g, f, hg, hM8, hf⟩

/-- Extended root data of the consumed degree-`7` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order — the deeper kills are in the fourth-face root
packet), and the NEW degree-`7` content is chamber-uniform in the
quotient `w` (`u` or `g`): the QUADRATIC root kill `w(a)² = 4 p₂(a)`
from the perfect-cube core, the value tie
`2048 q₄(a) = 3840 p₁ p₂ w - 320 p₁ w³ + 256 κ p₂²` at `a`, and its
reduction on the kill `128 q₄(a) = 40 p₁(a) w(a)³ + κ w(a)⁴` — `q₄`
does NOT vanish and no new vanishing is claimed. -/
theorem normalized410ScaleTwo_alignedSixthRow_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (a : K) (κ : K), H.eval a = 0 ∧
      (8 : K[X]) * q.coeff 8 =
        H * ((15 : K[X]) * p.coeff 3 ^ 2 +
          (20 : K[X]) * p.coeff 2 * H ^ 2 + Polynomial.C κ * H ^ 3) ∧
      (p.coeff 3).eval a = 0 ∧
      (q.coeff 8).derivative.eval a = 0 ∧
      ((∃ h0 u v : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (2048 : K) * (q.coeff 4).eval a =
            (3840 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
                u.eval a -
              (320 : K) * (p.coeff 1).eval a * u.eval a ^ 3 +
              (256 : K) * κ * (p.coeff 2).eval a ^ 2 ∧
          (128 : K) * (q.coeff 4).eval a =
            (40 : K) * (p.coeff 1).eval a * u.eval a ^ 3 +
              κ * u.eval a ^ 4) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ g f : K[X], p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (2048 : K) * (q.coeff 4).eval a =
              (3840 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
                  g.eval a -
                (320 : K) * (p.coeff 1).eval a * g.eval a ^ 3 +
                (256 : K) * κ * (p.coeff 2).eval a ^ 2 ∧
            (128 : K) * (q.coeff 4).eval a =
              (40 : K) * (p.coeff 1).eval a * g.eval a ^ 3 +
                κ * g.eval a ^ 4)) := by
  dsimp only at haligned ⊢
  have hHne : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  rcases hsource with
    ⟨hH, _hHdeg2, hPdegree, hQdegree, hp4, hq10, hKeller⟩
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
  have hclear := alignedSecondDefect_clearing_410 hM
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hHne
      simp [hHsq, hzero]
    obtain ⟨μ, _hμ2, hDform⟩ :=
      ninthPower_squareChamber_form_410 hH hHsq hrel
    have hdeg1 : h0.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hHsq
      rw [hHdegree, Polynomial.natDegree_pow] at hdegree
      omega
    have hkill0 : ∀ b : K, h0.eval b = 0 → (p.coeff 3).eval b = 0 := by
      intro b hb
      apply alignedThird_rootKill_p3_410 hrel
      rw [hHsq]
      simp only [Polynomial.eval_pow, hb]
      norm_num
    obtain ⟨t, ht⟩ := natDegree_one_dvd_of_root_kill_410 hdeg1 hkill0
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore := alignedSquareFourth_core_410 hh0 hHsq ht hDform hM4
    obtain ⟨u, hu, _hq6⟩ :=
      alignedSquareFourth_descent_410 hh0 hdeg1 hcore
    have hp3 : p.coeff 3 = h0 ^ 2 * u := by rw [ht, hu]; ring
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₂, _hμ₂2, hM6form⟩ :=
      fifteenthPower_squareChamber_form_410 hh0 hHsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedSquareSixth_core_410 hh0 hHsq hp3 hDform hM4 hM6form hM8form
    obtain ⟨v, hv, hq4⟩ :=
      alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hHroot : H.eval a = 0 := by
      rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hp3, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hHroot
    have hp3d : (p.coeff 3).derivative.eval a = 0 :=
      derivative_eval_eq_zero_of_pow_factor_410
        (by norm_num : 2 ≤ 2) hp3 hroot
    have hkilla : u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hv
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hq4tie : (2048 : K) * (q.coeff 4).eval a =
        (3840 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
            u.eval a -
          (320 : K) * (p.coeff 1).eval a * u.eval a ^ 3 +
          (256 : K) * κ * (p.coeff 2).eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq4
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq4tie' : (128 : K) * (q.coeff 4).eval a =
        (40 : K) * (p.coeff 1).eval a * u.eval a ^ 3 +
          κ * u.eval a ^ 4 := by
      linear_combination (1 / 16 : K) * hq4tie -
        ((60 : K) * (p.coeff 1).eval a * u.eval a +
          κ * (u.eval a ^ 2 + (4 : K) * (p.coeff 2).eval a)) * hkilla
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨h0, u, v, hh0, hHsq, hroot, hp3, hv, hp3d, hkilla,
        hq4tie, hq4tie'⟩⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    obtain ⟨_hκ₂, hD0⟩ :=
      ninthPower_nonsquareChamber_kill_410 hH hnsq hrel
    have hsimple : ∀ b : K, H.eval b = 0 → H.derivative.eval b ≠ 0 :=
      fun b hb =>
        nonsquare_natDegree_two_derivative_ne_zero hHdegree hnsq hb
    have hkill : ∀ b : K, H.eval b = 0 → (p.coeff 3).eval b = 0 :=
      fun b hb => alignedThird_rootKill_p3_410 hrel hb
    obtain ⟨g, hg⟩ :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple hkill
    obtain ⟨κ₃, hM4⟩ :=
      alignedFourthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨κ₄, hM6rel⟩ :=
      alignedFifthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₄, hM60⟩ :=
      fifteenthPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM6rel
    obtain ⟨κ₅, hM8form⟩ :=
      alignedSixthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore6 :=
      alignedNonsquareSixth_core_410 hH hg hD0 hM4 hM60 hM8form
    obtain ⟨f, hf, hq4⟩ :=
      alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hHne, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hp3a : (p.coeff 3).eval a = 0 := by
      rw [hg, Polynomial.eval_mul, hroot, zero_mul]
    have hq8d := alignedThird_q8_secondOrderKill_410 hM hrel hroot
    have hkilla : g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hf
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hq4tie : (2048 : K) * (q.coeff 4).eval a =
        (3840 : K) * (p.coeff 1).eval a * (p.coeff 2).eval a *
            g.eval a -
          (320 : K) * (p.coeff 1).eval a * g.eval a ^ 3 +
          (256 : K) * κ * (p.coeff 2).eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq4
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq4tie' : (128 : K) * (q.coeff 4).eval a =
        (40 : K) * (p.coeff 1).eval a * g.eval a ^ 3 +
          κ * g.eval a ^ 4 := by
      linear_combination (1 / 16 : K) * hq4tie -
        ((60 : K) * (p.coeff 1).eval a * g.eval a +
          κ * (g.eval a ^ 2 + (4 : K) * (p.coeff 2).eval a)) * hkilla
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, g, f, hg, hf, hkilla, hq4tie, hq4tie'⟩⟩

#print axioms alignedSixthCoefficientJacobianRow_410
#print axioms alignedSixthDefect_weightedDerivative_identity_410
#print axioms alignedSixthDefectRow_eq_zero_410
#print axioms ninthPowerRelation_of_weightNineRow_410
#print axioms alignedSixthDefectPowerRelation_410
#print axioms alignedSquareSixth_core_410
#print axioms alignedSquareSixth_descent_410
#print axioms alignedNonsquareSixth_core_410
#print axioms alignedNonsquareSixth_descent_410
#print axioms normalized410ScaleTwo_alignedSixthRow_packet
#print axioms normalized410ScaleTwo_alignedSixthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedSixthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedSixthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedSixthRow_rootData

end Max11DegreeRoutes
