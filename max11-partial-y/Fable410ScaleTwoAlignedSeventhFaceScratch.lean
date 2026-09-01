import Fable410ScaleTwoAlignedSixthFaceScratch

/-! # Seventh aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedSixthFaceScratch` consumed the degree-`6`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`21/2` first integral `M₁₀² = κ₆ H²¹` of the seventh defect, the
divisibility `80 u v³ - μ (35 u⁴ - 336 p₂ u² + 1344 p₂²) = h₀ s`, and
the solved cubic coefficient `q₃`.  This file consumes the next unused
aligned row, the degree-`5` Jacobian coefficient — the first row that
sees `q₂` — derived here directly from the literal Keller bracket.

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` through degree-`6` brackets of `M₂`, `M₄`,
`M₆`, `M₈`, and `M₁₀`, the degree-`5` row is the weighted derivative of
the cleared eighth defect

`M₁₂ = 245760 p₀² H¹² - 131072 q₂ H¹¹ + 245760 p₀ p₁ p₃ H¹⁰
  + 122880 p₀ p₂² H¹⁰ + 122880 p₁² p₂ H¹⁰ - 61440 p₀ p₂ p₃² H⁸
  - 30720 p₁² p₃² H⁸ - 61440 p₁ p₂² p₃ H⁸ - 5120 p₂⁴ H⁸
  + 7680 p₀ p₃⁴ H⁶ + 30720 p₁ p₂ p₃³ H⁶ + 15360 p₂³ p₃² H⁶
  - 3840 p₁ p₃⁵ H⁴ - 9600 p₂² p₃⁴ H⁴ + 2240 p₂ p₃⁶ H² - 180 p₃⁸
  + κ (32768 p₀ p₂ H¹¹ + 16384 p₁² H¹¹)
  - 3 p₃ M₁₀ - 64 p₂ H² M₈ - (320 p₁ H⁴ + 80 p₂ p₃ H² - 10 p₃³) M₆
  - (1536 p₀ H⁶ + 768 p₁ p₃ H⁴ + 384 p₂² H⁴ - 192 p₂ p₃² H²
    + 24 p₃⁴) M₄
  - (10752 p₀ p₃ H⁶ + 10752 p₁ p₂ H⁶ - 1344 p₁ p₃² H⁴ - 1344 p₂² p₃ H⁴
    + 560 p₂ p₃³ H² - 63 p₃⁵) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect that is QUADRATIC in `p₀` (leading term `245760 p₀² H¹²`), and
the first whose `κ`-module sees `p₁²` — via the exact multiplier
identity

`32768 H¹⁰ · row₅[p₄ = H²] = (H M₁₂' - 12 M₁₂ H')
  + 3 p₃ (2 H M₁₀' - 21 M₁₀ H')
  + (96 p₂ H² + 48 p₃²) (H M₈' - 9 M₈ H')
  + (192 p₁ H⁴ + 240 p₂ p₃ H² + 10 p₃³) (2 H M₆' - 15 M₆ H')
  + (1536 p₀ H⁶ + 2304 p₁ p₃ H⁴ + 1152 p₂² H⁴ + 576 p₂ p₃² H²
    - 24 p₃⁴) (H M₄' - 6 M₄ H')
  + (10752 p₀ p₃ H⁶ + 10752 p₁ p₂ H⁶ + 4032 p₁ p₃² H⁴ + 4032 p₂² p₃ H⁴
    - 336 p₂ p₃³ H² + 21 p₃⁵) (2 H M₂' - 9 M₂ H')`.

The correction module is EMPTY again: neither the aligned-face residual
`N` nor the degree-`11` relation `R` appears — the row's letters stop
at `q₆`, so no bracket combination can carry `q₈` or `q₉`, and the
identity is exact in the free letters.  On the aligned face every
previous bracket vanishes, so `H M₁₂' = 12 M₁₂ H'` and the EVEN-TYPE
weight-`12` polynomial first integral

`M₁₂ = κ₇ H¹²`

holds for a preserved constant `κ₇` — chamber-free, with no square-root
extraction and no parity split, like `M₄ = κ₃ H⁶` and `M₈ = κ₅ H⁹`.
The chamber core, after cancelling `h₀¹⁶` resp. `H⁸`, is the previous
face's perfect cube times a NEW quadratic cofactor:

`-20 (w² - 4 p₂)³ (9 w² - 4 p₂) - 3840 core p₁ w (w² - 4 p₂)²  + …`

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`: on
  the consumed divisibility `u² - 4 p₂ = h₀ v` the peel is THREE deep
  (q₂ sits six levels above the core against the divisibility's four):
  the NEW μ-loaded divisibility
  `20 (9 u² - 4 p₂) v³ - μ (63 u⁵ - 560 p₂ u³ + 1344 p₂² u) = h₀ s₂` —
  self-similar to the sixth face's `s`-divisibility one level down —
  then the explicit peels `s₂ + 3840 p₁ u v² = h₀ s₃` and
  `(10 μ₂ u + 1344 μ p₁)(u² - 8 p₂) - s₃ - 30720 p₁² v = h₀ s₄`, and
  the solved row with no `h₀` factor on `q₂`:
  `131072 q₂ = s₄ + 245760 p₀ p₁ u + κ (32768 p₀ p₂ + 16384 p₁²)
  - 64 κ₅ p₂ - 768 κ₃ p₁ u + (7680 p₀ - 24 κ₃) v²
  - h₀ (3 μ₃ u + 320 μ₂ p₁ + 10752 μ p₀ u)
  + h₀² (245760 p₀² - 1536 κ₃ p₀ - κ₇)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`, `M₆ = 0`, `M₁₀ = 0`, `M₄ = κ₃ H⁶`,
  `M₈ = κ₅ H⁹`, `M₁₂ = κ₇ H¹²`: on the consumed divisibility
  `g² - 4 p₂ = H f` the row is solved OUTRIGHT — no new letter and no
  new divisibility:
  `131072 q₂ = 245760 p₀ p₁ g + κ (32768 p₀ p₂ + 16384 p₁²) - 64 κ₅ p₂
  - 768 κ₃ p₁ g - 20 f³ (9 g² - 4 p₂) - 3840 p₁ g f² - 30720 p₁² f
  + H ((7680 p₀ - 24 κ₃) f² + 245760 p₀² - 1536 κ₃ p₀ - κ₇)`.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
tie `160 u(a)² v(a)³ = 7 μ u(a)⁵`, whose clash with the sixth face's
product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a factor-`10` mismatch
in the leading coefficient) forces the NEW ROOT DICHOTOMY

`(u(a) = 0 ∧ p₂(a) = 0)  ∨  (v(a) = 0 ∧ μ = 0)`

— the first aligned root branch that either pins `p₂(a) = 0` or kills
the square-chamber residual `μ` outright; on it `s₂(a) = 0`
unconditionally, and the ties `s₃(a) = -10 μ₂ u³ - 1344 μ p₁ u²
- 30720 p₁² v` and `131072 q₂(a) = s₄(a) + 245760 p₀ p₁ u
+ 8192 κ p₀ u² + 16384 κ p₁² - 16 κ₅ u² - 768 κ₃ p₁ u + 7680 p₀ v²
- 24 κ₃ v²` follow.  The nonsquare chamber gains the closed value tie
`131072 q₂(a) = 245760 p₀ p₁ g + 8192 κ p₀ g² + 16384 κ p₁²
- 16 κ₅ g² - 768 κ₃ p₁ g - 160 f³ g² - 3840 p₁ g f² - 30720 p₁² f` —
the first aligned root tie that sees `κ₅`.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`,
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, and the sixth-face divisibility carrying `s`.  The
weight-`12` Wronskian quotient
`twelfthPowerRelation_of_weightTwelveRow_410` is new but generic.

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₂ = 0`, `μ = 0`, `μ₂ = 0`, `μ₃ = 0`, `κ = 0` through
`κ₇ = 0`) are not excluded, and the constants are preserved where not
previously forced.  `p₀, p₁, p₂` are constrained only through the
solved forms and the divisibilities.  The next unused Keller row on the
aligned face is the degree-`4` Jacobian coefficient, the first row that
sees `q₁`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`5` Keller coefficient on the aligned face -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`5` Jacobian coefficient, the first
aligned row that sees `q₂`.  It is derived directly from the Keller
bracket. -/
theorem alignedEighthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} :
        Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-! ## Aligned eighth defect -/

/-- Cleared eighth defect of the degree-`5` aligned `(4,10)` row, kept
in factored form through the third through seventh defects `M₂`, `M₄`,
`M₆`, `M₈`, and `M₁₀`:
`M₁₂ = 245760 p₀² H¹² - 131072 q₂ H¹¹ + 245760 p₀ p₁ p₃ H¹⁰
+ 122880 p₀ p₂² H¹⁰ + 122880 p₁² p₂ H¹⁰ - 61440 p₀ p₂ p₃² H⁸
- 30720 p₁² p₃² H⁸ - 61440 p₁ p₂² p₃ H⁸ - 5120 p₂⁴ H⁸ + 7680 p₀ p₃⁴ H⁶
+ 30720 p₁ p₂ p₃³ H⁶ + 15360 p₂³ p₃² H⁶ - 3840 p₁ p₃⁵ H⁴
- 9600 p₂² p₃⁴ H⁴ + 2240 p₂ p₃⁶ H² - 180 p₃⁸
+ κ (32768 p₀ p₂ + 16384 p₁²) H¹¹ - 3 p₃ M₁₀ - 64 p₂ H² M₈
- (320 p₁ H⁴ + 80 p₂ p₃ H² - 10 p₃³) M₆
- (1536 p₀ H⁶ + 768 p₁ p₃ H⁴ + 384 p₂² H⁴ - 192 p₂ p₃² H² + 24 p₃⁴) M₄
- (10752 p₀ p₃ H⁶ + 10752 p₁ p₂ H⁶ - 1344 p₁ p₃² H⁴ - 1344 p₂² p₃ H⁴
+ 560 p₂ p₃³ H² - 63 p₃⁵) M₂`.  Every monomial has exact `H`-weight
`12`; it is the first aligned defect quadratic in `p₀`, and the first
whose `κ`-module sees `p₁²`. -/
def alignedEighthDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (245760 : K[X]) * a0 ^ 2 * H ^ 12 - (131072 : K[X]) * b2 * H ^ 11 +
    (245760 : K[X]) * a0 * a1 * a3 * H ^ 10 +
    (122880 : K[X]) * a0 * a2 ^ 2 * H ^ 10 +
    (122880 : K[X]) * a1 ^ 2 * a2 * H ^ 10 -
    (61440 : K[X]) * a0 * a2 * a3 ^ 2 * H ^ 8 -
    (30720 : K[X]) * a1 ^ 2 * a3 ^ 2 * H ^ 8 -
    (61440 : K[X]) * a1 * a2 ^ 2 * a3 * H ^ 8 -
    (5120 : K[X]) * a2 ^ 4 * H ^ 8 +
    (7680 : K[X]) * a0 * a3 ^ 4 * H ^ 6 +
    (30720 : K[X]) * a1 * a2 * a3 ^ 3 * H ^ 6 +
    (15360 : K[X]) * a2 ^ 3 * a3 ^ 2 * H ^ 6 -
    (3840 : K[X]) * a1 * a3 ^ 5 * H ^ 4 -
    (9600 : K[X]) * a2 ^ 2 * a3 ^ 4 * H ^ 4 +
    (2240 : K[X]) * a2 * a3 ^ 6 * H ^ 2 - (180 : K[X]) * a3 ^ 8 +
    Polynomial.C κ *
      ((32768 : K[X]) * a0 * a2 * H ^ 11 +
        (16384 : K[X]) * a1 ^ 2 * H ^ 11) -
    (3 : K[X]) * a3 *
      alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ -
    (64 : K[X]) * a2 * H ^ 2 *
      alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ -
    ((320 : K[X]) * a1 * H ^ 4 + (80 : K[X]) * a2 * a3 * H ^ 2 -
      (10 : K[X]) * a3 ^ 3) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((1536 : K[X]) * a0 * H ^ 6 + (768 : K[X]) * a1 * a3 * H ^ 4 +
      (384 : K[X]) * a2 ^ 2 * H ^ 4 - (192 : K[X]) * a2 * a3 ^ 2 * H ^ 2 +
      (24 : K[X]) * a3 ^ 4) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((10752 : K[X]) * a0 * a3 * H ^ 6 + (10752 : K[X]) * a1 * a2 * H ^ 6 -
      (1344 : K[X]) * a1 * a3 ^ 2 * H ^ 4 -
      (1344 : K[X]) * a2 ^ 2 * a3 * H ^ 4 +
      (560 : K[X]) * a2 * a3 ^ 3 * H ^ 2 - (63 : K[X]) * a3 ^ 5) *
      alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`5` Jacobian expression with the
weight-`12` bracket of `M₁₂`.  The only corrections are the consumed
degree-`10` through degree-`6` brackets of `M₂`, `M₄`, `M₆`, `M₈`, and
`M₁₀`: neither the aligned-face residual `N` nor the degree-`11`
relation `R` appears at all — the correction module is empty for the
second row in a row.  Every correction vanishes on the aligned face. -/
theorem alignedEighthDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (32768 : K[X]) * H ^ 10 *
        ((H ^ 2).derivative * (b2 * (2 : K[X])) +
          a3.derivative * (b3 * (3 : K[X])) +
          a2.derivative * (b4 * (4 : K[X])) +
          a1.derivative * (b5 * (5 : K[X])) +
          a0.derivative * (b6 * (6 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b2.derivative +
          (a3 * (3 : K[X])) * b3.derivative +
          (a2 * (2 : K[X])) * b4.derivative +
          a1 * b5.derivative)) =
      (H * (alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (12 : K[X]) *
          alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (3 : K[X]) * a3 *
          ((2 : K[X]) * H *
              (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) *
              alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((96 : K[X]) * a2 * H ^ 2 + (48 : K[X]) * a3 ^ 2) *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((192 : K[X]) * a1 * H ^ 4 + (240 : K[X]) * a2 * a3 * H ^ 2 +
            (10 : K[X]) * a3 ^ 3) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((1536 : K[X]) * a0 * H ^ 6 + (2304 : K[X]) * a1 * a3 * H ^ 4 +
            (1152 : K[X]) * a2 ^ 2 * H ^ 4 +
            (576 : K[X]) * a2 * a3 ^ 2 * H ^ 2 -
            (24 : K[X]) * a3 ^ 4) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((10752 : K[X]) * a0 * a3 * H ^ 6 + (10752 : K[X]) * a1 * a2 * H ^ 6 +
            (4032 : K[X]) * a1 * a3 ^ 2 * H ^ 4 +
            (4032 : K[X]) * a2 ^ 2 * a3 * H ^ 4 -
            (336 : K[X]) * a2 * a3 ^ 3 * H ^ 2 + (21 : K[X]) * a3 ^ 5) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [alignedEighthDefect410, alignedSeventhDefect410,
    alignedSixthDefect410, alignedFifthDefect410, alignedFourthDefect410,
    alignedThirdDefect410,
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
degree-`6` rows, the degree-`5` row is the weighted derivative
`H M₁₂' - 12 M₁₂ H' = 0`. -/
theorem alignedEighthDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    H * (alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (12 : K[X]) *
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEighthCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6] at hrow
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB8 :=
    alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB10 :=
    alignedSeventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedEighthDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 2)
    (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8, hB10] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Weight-twelve polynomial first integral -/

/-- Generic Wronskian quotient for the weight-twelve bracket: over a
characteristic-zero field, `H D' - 12 D H' = 0` forces
`D = C c * H¹²`.  The bracket is first-order, so the integral needs no
square root of `H` and no parity split. -/
theorem twelfthPowerRelation_of_weightTwelveRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : H * D.derivative - (12 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D = Polynomial.C c * H ^ 12 := by
  have hC12 : Polynomial.C (12 : K) = (12 : K[X]) :=
    Polynomial.C_eq_natCast 12
  have hW : Polynomial.wronskian D (H ^ 12) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      D * (Polynomial.C (12 : K) * H ^ (12 - 1) * H.derivative) -
          D.derivative * H ^ 12 =
          H ^ 11 *
            (Polynomial.C (12 : K) * D * H.derivative -
              H * D.derivative) := by ring
      _ = 0 := by
        rw [hC12]
        have hfac :
            (12 : K[X]) * D * H.derivative - H * D.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 12 hH) hW

/-- Weight-twelve polynomial first integral of the aligned `(4,10)`
eighth defect: `M₁₂ = κ₇ H¹²` — even-type and chamber-free, one level
below the odd twenty-first-power shape of the degree-`6` row. -/
theorem alignedEighthDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₇ : K,
      alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₇ * H ^ 12 :=
  twelfthPowerRelation_of_weightTwelveRow_410 hH
    (alignedEighthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Square chamber -/

/-- Cleared square-core form of the eighth defect relation: cancelling
`h₀¹⁶` from `M₁₂ = κ₇ h₀²⁴` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
`M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹` exposes the `h₀`-free
core `-20 (u² - 4 p₂)³ (9 u² - 4 p₂) - 3840 h₀² p₁ u (u² - 4 p₂)²` —
the previous face's perfect cube times a NEW quadratic cofactor —
carried by `h₀³` against the explicit quotient, whose leading block is
the μ-loaded quintic `63 u⁵ - 560 p₂ u³ + 1344 p₂² u`. -/
theorem alignedSquareEighth_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hp3 : a3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H a1 a2 a3 b7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM6 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
      Polynomial.C μ₂ * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM10 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
      Polynomial.C μ₃ * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12) :
    (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
          (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (3840 : K[X]) * h0 ^ 2 * a1 * u * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((63 : K[X]) * u ^ 5 - (560 : K[X]) * a2 * u ^ 3 +
              (1344 : K[X]) * a2 ^ 2 * u) +
          h0 * (((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) *
              (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (30720 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
          h0 ^ 2 *
            ((Polynomial.C μ₂ * ((10 : K[X]) * u) +
              Polynomial.C μ * ((1344 : K[X]) * a1)) *
              (u ^ 2 - (8 : K[X]) * a2)) +
          h0 ^ 3 * ((245760 : K[X]) * a0 * a1 * u +
            Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
              (16384 : K[X]) * a1 ^ 2) -
            Polynomial.C κ₅ * ((64 : K[X]) * a2) -
            Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) -
            (131072 : K[X]) * b2) -
          h0 ^ 4 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
            Polynomial.C μ₂ * ((320 : K[X]) * a1) +
            Polynomial.C μ * ((10752 : K[X]) * a0 * u)) +
          h0 ^ 5 * ((245760 : K[X]) * a0 ^ 2 -
            Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
            Polynomial.C κ₇)) := by
  have hM12' := hM12
  simp only [alignedEighthDefect410] at hM12'
  rw [hM10, hM8, hM6, hM4, hM2, hHsq, hp3] at hM12'
  apply mul_left_cancel₀ (pow_ne_zero 16 hh0)
  linear_combination -hM12'

/-- The consumed degree-`5` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the fifth face the core gains `h₀³`,
and the peel is three deep: the NEW μ-loaded divisibility
`20 (9 u² - 4 p₂) v³ - μ (63 u⁵ - 560 p₂ u³ + 1344 p₂² u) = h₀ s₂` —
self-similar to the sixth face's `s`-divisibility — then the explicit
peels producing `s₃` and `s₄`, and the solved quadratic row.  The new
letter `q₂` carries no `h₀` factor. -/
theorem alignedSquareEighth_solved_410 {K : Type*} [Field K] [CharZero K]
    {h0 u v a0 a1 a2 b2 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ κ₇ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * a2) *
            (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (3840 : K[X]) * h0 ^ 2 * a1 * u *
            (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((63 : K[X]) * u ^ 5 - (560 : K[X]) * a2 * u ^ 3 +
                (1344 : K[X]) * a2 ^ 2 * u) +
            h0 * (((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) *
                (u ^ 2 - (4 : K[X]) * a2) ^ 2 -
              (30720 : K[X]) * a1 ^ 2 * (u ^ 2 - (4 : K[X]) * a2)) +
            h0 ^ 2 *
              ((Polynomial.C μ₂ * ((10 : K[X]) * u) +
                Polynomial.C μ * ((1344 : K[X]) * a1)) *
                (u ^ 2 - (8 : K[X]) * a2)) +
            h0 ^ 3 * ((245760 : K[X]) * a0 * a1 * u +
              Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
                (16384 : K[X]) * a1 ^ 2) -
              Polynomial.C κ₅ * ((64 : K[X]) * a2) -
              Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) -
              (131072 : K[X]) * b2) -
            h0 ^ 4 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
              Polynomial.C μ₂ * ((320 : K[X]) * a1) +
              Polynomial.C μ * ((10752 : K[X]) * a0 * u)) +
            h0 ^ 5 * ((245760 : K[X]) * a0 ^ 2 -
              Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
              Polynomial.C κ₇)))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s₂ s₃ s₄ : K[X],
      (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * a2) * v ^ 3 -
          Polynomial.C μ *
            ((63 : K[X]) * u ^ 5 - (560 : K[X]) * a2 * u ^ 3 +
              (1344 : K[X]) * a2 ^ 2 * u) = h0 * s₂ ∧
      s₂ + (3840 : K[X]) * a1 * u * v ^ 2 = h0 * s₃ ∧
      (Polynomial.C μ₂ * ((10 : K[X]) * u) +
          Polynomial.C μ * ((1344 : K[X]) * a1)) *
          (u ^ 2 - (8 : K[X]) * a2) -
        s₃ - (30720 : K[X]) * a1 ^ 2 * v = h0 * s₄ ∧
      (131072 : K[X]) * b2 =
        s₄ + (245760 : K[X]) * a0 * a1 * u +
          Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
            (16384 : K[X]) * a1 ^ 2) -
          Polynomial.C κ₅ * ((64 : K[X]) * a2) -
          Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) +
          ((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) * v ^ 2 -
          h0 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
            Polynomial.C μ₂ * ((320 : K[X]) * a1) +
            Polynomial.C μ * ((10752 : K[X]) * a0 * u)) +
          h0 ^ 2 * ((245760 : K[X]) * a0 ^ 2 -
            Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
            Polynomial.C κ₇) := by
  refine ⟨-(3840 : K[X]) * a1 * u * v ^ 2 +
      ((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) * h0 ^ 2 *
        v ^ 2 -
      (30720 : K[X]) * a1 ^ 2 * h0 * v +
      h0 * ((Polynomial.C μ₂ * ((10 : K[X]) * u) +
        Polynomial.C μ * ((1344 : K[X]) * a1)) *
        (u ^ 2 - (8 : K[X]) * a2)) +
      h0 ^ 2 * ((245760 : K[X]) * a0 * a1 * u +
        Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
          (16384 : K[X]) * a1 ^ 2) -
        Polynomial.C κ₅ * ((64 : K[X]) * a2) -
        Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) -
        (131072 : K[X]) * b2) -
      h0 ^ 3 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
        Polynomial.C μ₂ * ((320 : K[X]) * a1) +
        Polynomial.C μ * ((10752 : K[X]) * a0 * u)) +
      h0 ^ 4 * ((245760 : K[X]) * a0 ^ 2 -
        Polynomial.C κ₃ * ((1536 : K[X]) * a0) - Polynomial.C κ₇),
    ((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) * h0 * v ^ 2 -
      (30720 : K[X]) * a1 ^ 2 * v +
      (Polynomial.C μ₂ * ((10 : K[X]) * u) +
        Polynomial.C μ * ((1344 : K[X]) * a1)) *
        (u ^ 2 - (8 : K[X]) * a2) +
      h0 * ((245760 : K[X]) * a0 * a1 * u +
        Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
          (16384 : K[X]) * a1 ^ 2) -
        Polynomial.C κ₅ * ((64 : K[X]) * a2) -
        Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) -
        (131072 : K[X]) * b2) -
      h0 ^ 2 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
        Polynomial.C μ₂ * ((320 : K[X]) * a1) +
        Polynomial.C μ * ((10752 : K[X]) * a0 * u)) +
      h0 ^ 3 * ((245760 : K[X]) * a0 ^ 2 -
        Polynomial.C κ₃ * ((1536 : K[X]) * a0) - Polynomial.C κ₇),
    -((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) * v ^ 2 -
      ((245760 : K[X]) * a0 * a1 * u +
        Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
          (16384 : K[X]) * a1 ^ 2) -
        Polynomial.C κ₅ * ((64 : K[X]) * a2) -
        Polynomial.C κ₃ * ((768 : K[X]) * a1 * u) -
        (131072 : K[X]) * b2) +
      h0 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
        Polynomial.C μ₂ * ((320 : K[X]) * a1) +
        Polynomial.C μ * ((10752 : K[X]) * a0 * u)) -
      h0 ^ 2 * ((245760 : K[X]) * a0 ^ 2 -
        Polynomial.C κ₃ * ((1536 : K[X]) * a0) - Polynomial.C κ₇),
    ?_, ?_, ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    linear_combination hcore
  · ring
  · ring
  · ring

/-! ## Nonsquare chamber -/

/-- Cleared nonsquare-core form of the eighth defect relation:
cancelling `H⁸` from `M₁₂ = κ₇ H¹²` on `p₃ = H g`, `M₂ = 0`,
`M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`, `M₁₀ = 0` exposes the same core
`-20 (g² - 4 p₂)³ (9 g² - 4 p₂) - 3840 H p₁ g (g² - 4 p₂)²` carried by
`H²` against the explicit quotient. -/
theorem alignedNonsquareEighth_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0)
    (hM12 : alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
      Polynomial.C κ₇ * H ^ 12) :
    (20 : K[X]) * ((9 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
          (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (3840 : K[X]) * H * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        (((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
          (30720 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) +
          H * ((245760 : K[X]) * a0 * a1 * g +
            Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
              (16384 : K[X]) * a1 ^ 2) -
            Polynomial.C κ₅ * ((64 : K[X]) * a2) -
            Polynomial.C κ₃ * ((768 : K[X]) * a1 * g) -
            (131072 : K[X]) * b2) +
          H ^ 2 * ((245760 : K[X]) * a0 ^ 2 -
            Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
            Polynomial.C κ₇)) := by
  have hM12' := hM12
  simp only [alignedEighthDefect410] at hM12'
  rw [hM100, hM8, hM60, hM4, hM20, hg] at hM12'
  apply mul_left_cancel₀ (pow_ne_zero 8 hH)
  linear_combination -hM12'

/-- The consumed degree-`5` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` of the fifth face the quadratic row is
solved OUTRIGHT — no new letter, no new divisibility, and `q₂` carries
no `H` factor. -/
theorem alignedNonsquareEighth_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 b2 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (hH : H ≠ 0)
    (hcore :
      (20 : K[X]) * ((9 : K[X]) * g ^ 2 - (4 : K[X]) * a2) *
            (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (3840 : K[X]) * H * a1 * g * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          (((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) *
              (g ^ 2 - (4 : K[X]) * a2) ^ 2 -
            (30720 : K[X]) * a1 ^ 2 * (g ^ 2 - (4 : K[X]) * a2) +
            H * ((245760 : K[X]) * a0 * a1 * g +
              Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
                (16384 : K[X]) * a1 ^ 2) -
              Polynomial.C κ₅ * ((64 : K[X]) * a2) -
              Polynomial.C κ₃ * ((768 : K[X]) * a1 * g) -
              (131072 : K[X]) * b2) +
            H ^ 2 * ((245760 : K[X]) * a0 ^ 2 -
              Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
              Polynomial.C κ₇)))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (131072 : K[X]) * b2 =
      (245760 : K[X]) * a0 * a1 * g +
        Polynomial.C κ * ((32768 : K[X]) * a0 * a2 +
          (16384 : K[X]) * a1 ^ 2) -
        Polynomial.C κ₅ * ((64 : K[X]) * a2) -
        Polynomial.C κ₃ * ((768 : K[X]) * a1 * g) -
        (20 : K[X]) * f ^ 3 *
          ((9 : K[X]) * g ^ 2 - (4 : K[X]) * a2) -
        (3840 : K[X]) * a1 * g * f ^ 2 -
        (30720 : K[X]) * a1 ^ 2 * f +
        H * (((7680 : K[X]) * a0 - Polynomial.C κ₃ * (24 : K[X])) *
            f ^ 2 +
          (245760 : K[X]) * a0 ^ 2 -
          Polynomial.C κ₃ * ((1536 : K[X]) * a0) -
          Polynomial.C κ₇) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination hcore

/-! ## Source-facing eighth-row packets -/

/-- Source-facing weight-`12` integral of a normalized aligned scale-two
`(4,10)` source: the degree-`5` row is consumed into `M₁₂ = κ₇ H¹²` on
top of the previous aligned packet, together with the chamber-free root
jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedEighthRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ : K,
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
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 = Polynomial.C κ₆ * H ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
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
  obtain ⟨κ₆, hM10⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨κ₇, hM12⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10, hM12,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber eighth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free weight-`12` form `M₁₂ = κ₇ H¹²`, the NEW μ-loaded
divisibility `20 (9 u² - 4 p₂) v³ - μ (63 u⁵ - 560 p₂ u³ + 1344 p₂² u)
= h₀ s₂`, the explicit peels producing `s₃` and `s₄`, and the solved
quadratic row.  The constants `μ`, `κ₃`, `μ₂`, `κ₅`, `μ₃`, and `κ₇`
are preserved, not cleared, and `q₂` carries no `h₀` factor. -/
theorem normalized410ScaleTwo_alignedEighthRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ κ₇ : K) (u v s₂ s₃ s₄ : K[X]),
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
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = Polynomial.C μ₃ * h0 ^ 21 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) *
            v ^ 3 -
          Polynomial.C μ *
            ((63 : K[X]) * u ^ 5 - (560 : K[X]) * p.coeff 2 * u ^ 3 +
              (1344 : K[X]) * p.coeff 2 ^ 2 * u) = h0 * s₂ ∧
        s₂ + (3840 : K[X]) * p.coeff 1 * u * v ^ 2 = h0 * s₃ ∧
        (Polynomial.C μ₂ * ((10 : K[X]) * u) +
            Polynomial.C μ * ((1344 : K[X]) * p.coeff 1)) *
            (u ^ 2 - (8 : K[X]) * p.coeff 2) -
          s₃ - (30720 : K[X]) * p.coeff 1 ^ 2 * v = h0 * s₄ ∧
        (131072 : K[X]) * q.coeff 2 =
          s₄ + (245760 : K[X]) * p.coeff 0 * p.coeff 1 * u +
            Polynomial.C κ * ((32768 : K[X]) * p.coeff 0 * p.coeff 2 +
              (16384 : K[X]) * p.coeff 1 ^ 2) -
            Polynomial.C κ₅ * ((64 : K[X]) * p.coeff 2) -
            Polynomial.C κ₃ * ((768 : K[X]) * p.coeff 1 * u) +
            ((7680 : K[X]) * p.coeff 0 -
              Polynomial.C κ₃ * (24 : K[X])) * v ^ 2 -
            h0 * (Polynomial.C μ₃ * ((3 : K[X]) * u) +
              Polynomial.C μ₂ * ((320 : K[X]) * p.coeff 1) +
              Polynomial.C μ * ((10752 : K[X]) * p.coeff 0 * u)) +
            h0 ^ 2 * ((245760 : K[X]) * p.coeff 0 ^ 2 -
              Polynomial.C κ₃ * ((1536 : K[X]) * p.coeff 0) -
              Polynomial.C κ₇) := by
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
  obtain ⟨v, hv, _hq4⟩ := alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
    twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore8 :=
    alignedSquareEighth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form hM12form
  obtain ⟨s₂, s₃, s₄, hd1, hd2, hd3, hq2⟩ :=
    alignedSquareEighth_solved_410 hh0 hcore8 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, u, v, s₂, s₃, s₄, hp3, hDform, hM4,
    hM6form, hM8form, hM10form, hM12form, hv, hd1, hd2, hd3, hq2⟩

/-- Exact nonsquare-chamber eighth packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
chamber-free weight-`12` form `M₁₂ = κ₇ H¹²` (no parity kill at this
row), and the quadratic row solved OUTRIGHT on the fifth face's
divisibility `g² - 4 p₂ = H f` — no new letter and no new divisibility.
`q₂` carries no `H` factor. -/
theorem normalized410ScaleTwo_alignedEighthRow_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ : K) (g f : K[X]),
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
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 ∧
        alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₇ * H ^ 12 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        (131072 : K[X]) * q.coeff 2 =
          (245760 : K[X]) * p.coeff 0 * p.coeff 1 * g +
            Polynomial.C κ * ((32768 : K[X]) * p.coeff 0 * p.coeff 2 +
              (16384 : K[X]) * p.coeff 1 ^ 2) -
            Polynomial.C κ₅ * ((64 : K[X]) * p.coeff 2) -
            Polynomial.C κ₃ * ((768 : K[X]) * p.coeff 1 * g) -
            (20 : K[X]) * f ^ 3 *
              ((9 : K[X]) * g ^ 2 - (4 : K[X]) * p.coeff 2) -
            (3840 : K[X]) * p.coeff 1 * g * f ^ 2 -
            (30720 : K[X]) * p.coeff 1 ^ 2 * f +
            H * (((7680 : K[X]) * p.coeff 0 -
                Polynomial.C κ₃ * (24 : K[X])) * f ^ 2 +
              (245760 : K[X]) * p.coeff 0 ^ 2 -
              Polynomial.C κ₃ * ((1536 : K[X]) * p.coeff 0) -
              Polynomial.C κ₇) := by
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
  obtain ⟨f, hf, _hq4⟩ :=
    alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
  obtain ⟨κ₆, hM10rel⟩ :=
    alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  obtain ⟨_hκ₆, hM100⟩ :=
    twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
  obtain ⟨κ₇, hM12form⟩ :=
    alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
      haligned hM
  have hcore8 :=
    alignedNonsquareEighth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
      hM12form
  have hq2 := alignedNonsquareEighth_solved_410 hH hcore8 hf
  exact ⟨κ, κ₃, κ₅, κ₇, g, f, hg, hD0, hM4, hM60, hM8form, hM100,
    hM12form, hf, hq2⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`5`
aligned row: both chambers carry the chamber-free even integral
`M₁₂ = κ₇ H¹²`; the square chamber adds the NEW μ-loaded divisibility
carrying `s₂`, the nonsquare chamber solves the row outright on the
fifth face's divisibility.  Neither chamber is excluded and no closure
is claimed. -/
theorem normalized410ScaleTwo_alignedEighthRow_chamberDichotomy
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
      ∃ (κ μ κ₇ : K) (u v s₂ : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
              (q.coeff 7) κ = Polynomial.C μ * h0 ^ 9 ∧
          alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₇ * H ^ 12 ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) *
              v ^ 3 -
            Polynomial.C μ *
              ((63 : K[X]) * u ^ 5 - (560 : K[X]) * p.coeff 2 * u ^ 3 +
                (1344 : K[X]) * p.coeff 2 ^ 2 * u) = h0 * s₂) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₇ : K) (g f : K[X]),
        p.coeff 3 = H * g ∧
          alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4)
              (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₇ * H ^ 12 ∧
          g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedEighthRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, κ₇, u, v, s₂, s₃, s₄, hp3, hM2f,
      _hM4, _hM6f, _hM8, _hM10f, hM12, hv, hd1, _hd2, _hd3, _hq2⟩ :=
      hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₇, u, v, s₂, hp3, hM2f, hM12,
      hv, hd1⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedEighthRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, g, f, hg, _hM20, _hM4, _hM60, _hM8, _hM100,
      hM12, hf, _hq2⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₇, g, f, hg, hM12, hf⟩

/-- Extended root data of the consumed degree-`5` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order — the deeper kills are in the previous root
packets), and the NEW degree-`5` content splits by chamber.  The square
chamber gains the tie `160 u(a)² v(a)³ = 7 μ u(a)⁵`, whose clash with
the sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` forces
the NEW ROOT DICHOTOMY `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)` —
either `p₂(a)` is pinned to zero or the square residual `μ` is killed
outright — plus `s₂(a) = 0`, the `s₃` tie, and the `q₂` value ties.
The nonsquare chamber gains the closed value tie on `q₂` — the first
aligned root tie seeing `κ₅`.  `q₂` does NOT vanish and no new
vanishing is claimed; both dichotomy branches are preserved. -/
theorem normalized410ScaleTwo_alignedEighthRow_rootData
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
      ((∃ (μ μ₂ κ₃ κ₅ : K) (h0 u v s₂ s₃ s₄ : K[X]),
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧ h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (20 : K[X]) * ((9 : K[X]) * u ^ 2 - (4 : K[X]) * p.coeff 2) *
              v ^ 3 -
            Polynomial.C μ *
              ((63 : K[X]) * u ^ 5 - (560 : K[X]) * p.coeff 2 * u ^ 3 +
                (1344 : K[X]) * p.coeff 2 ^ 2 * u) = h0 * s₂ ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (160 : K) * u.eval a ^ 2 * v.eval a ^ 3 =
            (7 : K) * μ * u.eval a ^ 5 ∧
          ((u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
            (v.eval a = 0 ∧ μ = 0)) ∧
          s₂.eval a =
            -(3840 : K) * (p.coeff 1).eval a * u.eval a *
              v.eval a ^ 2 ∧
          s₂.eval a = 0 ∧
          s₃.eval a =
            -((10 : K) * μ₂ * u.eval a ^ 3) -
              (1344 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 2 -
              (30720 : K) * (p.coeff 1).eval a ^ 2 * v.eval a ∧
          (131072 : K) * (q.coeff 2).eval a =
            s₄.eval a +
              (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
                u.eval a +
              (32768 : K) * κ * (p.coeff 0).eval a *
                (p.coeff 2).eval a +
              (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
              (64 : K) * κ₅ * (p.coeff 2).eval a -
              (768 : K) * κ₃ * (p.coeff 1).eval a * u.eval a +
              (7680 : K) * (p.coeff 0).eval a * v.eval a ^ 2 -
              (24 : K) * κ₃ * v.eval a ^ 2 ∧
          (131072 : K) * (q.coeff 2).eval a =
            s₄.eval a +
              (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
                u.eval a +
              (8192 : K) * κ * (p.coeff 0).eval a * u.eval a ^ 2 +
              (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
              (16 : K) * κ₅ * u.eval a ^ 2 -
              (768 : K) * κ₃ * (p.coeff 1).eval a * u.eval a +
              (7680 : K) * (p.coeff 0).eval a * v.eval a ^ 2 -
              (24 : K) * κ₃ * v.eval a ^ 2) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ (κ₃ κ₅ : K) (g f : K[X]), p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (131072 : K) * (q.coeff 2).eval a =
              (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
                  g.eval a +
                (32768 : K) * κ * (p.coeff 0).eval a *
                  (p.coeff 2).eval a +
                (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
                (64 : K) * κ₅ * (p.coeff 2).eval a -
                (768 : K) * κ₃ * (p.coeff 1).eval a * g.eval a -
                (20 : K) * f.eval a ^ 3 *
                  ((9 : K) * g.eval a ^ 2 -
                    (4 : K) * (p.coeff 2).eval a) -
                (3840 : K) * (p.coeff 1).eval a * g.eval a *
                  f.eval a ^ 2 -
                (30720 : K) * (p.coeff 1).eval a ^ 2 * f.eval a ∧
            (131072 : K) * (q.coeff 2).eval a =
              (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
                  g.eval a +
                (8192 : K) * κ * (p.coeff 0).eval a * g.eval a ^ 2 +
                (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
                (16 : K) * κ₅ * g.eval a ^ 2 -
                (768 : K) * κ₃ * (p.coeff 1).eval a * g.eval a -
                (160 : K) * f.eval a ^ 3 * g.eval a ^ 2 -
                (3840 : K) * (p.coeff 1).eval a * g.eval a *
                  f.eval a ^ 2 -
                (30720 : K) * (p.coeff 1).eval a ^ 2 * f.eval a)) := by
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
    obtain ⟨v, hv, _hq4⟩ :=
      alignedSquareSixth_descent_410 hh0 hdeg1 hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨μ₃, _hμ₃2, hM10form⟩ :=
      twentyFirstPower_squareChamber_form_410 hh0 hHsq hM10rel
    have hcore7 :=
      alignedSquareSeventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form
    obtain ⟨s, hs, _hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore8 :=
      alignedSquareEighth_core_410 hh0 hHsq hp3 hDform hM4 hM6form
        hM8form hM10form hM12form
    obtain ⟨s₂, s₃, s₄, hd1, hd2, hd3, hq2⟩ :=
      alignedSquareEighth_solved_410 hh0 hcore8 hv
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
    have hμtie : (80 : K) * u.eval a * v.eval a ^ 3 =
        μ * ((35 : K) * u.eval a ^ 4 -
          (336 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
          (1344 : K) * (p.coeff 2).eval a ^ 2) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hs
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hkilltie : u.eval a *
        ((16 : K) * v.eval a ^ 3 - (7 : K) * μ * u.eval a ^ 3) = 0 := by
      linear_combination (1 / 5 : K) * hμtie -
        (336 / 5 : K) * μ * (p.coeff 2).eval a * hkilla
    have hd1a :
        (20 : K) * ((9 : K) * u.eval a ^ 2 -
            (4 : K) * (p.coeff 2).eval a) * v.eval a ^ 3 -
          μ * ((63 : K) * u.eval a ^ 5 -
            (560 : K) * (p.coeff 2).eval a * u.eval a ^ 3 +
            (1344 : K) * (p.coeff 2).eval a ^ 2 * u.eval a) = 0 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd1
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hnewtie : (160 : K) * u.eval a ^ 2 * v.eval a ^ 3 =
        (7 : K) * μ * u.eval a ^ 5 := by
      linear_combination hd1a +
        (-(20 : K) * v.eval a ^ 3 + (56 : K) * μ * u.eval a ^ 3 -
          (336 : K) * μ * u.eval a * (p.coeff 2).eval a) * hkilla
    have hdich : (u.eval a = 0 ∧ (p.coeff 2).eval a = 0) ∨
        (v.eval a = 0 ∧ μ = 0) := by
      by_cases hu : u.eval a = 0
      · refine Or.inl ⟨hu, ?_⟩
        have h4 : (4 : K) * (p.coeff 2).eval a = 0 := by
          rw [← hkilla, hu]
          ring
        exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
      · have h16 : (16 : K) * v.eval a ^ 3 -
            (7 : K) * μ * u.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp hkilltie).resolve_left hu
        have h144 : (144 : K) * (u.eval a ^ 2 * v.eval a ^ 3) = 0 := by
          linear_combination hnewtie - u.eval a ^ 2 * h16
        have huv : u.eval a ^ 2 * v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp h144).resolve_left (by norm_num)
        have hv3 : v.eval a ^ 3 = 0 :=
          (mul_eq_zero.mp huv).resolve_left (pow_ne_zero 2 hu)
        have hv0 : v.eval a = 0 :=
          pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hv3
        have h7 : ((7 : K) * μ) * u.eval a ^ 3 = 0 := by
          linear_combination -h16 + (16 : K) * hv3
        have h7μ : (7 : K) * μ = 0 :=
          (mul_eq_zero.mp h7).resolve_right (pow_ne_zero 3 hu)
        have hμ0 : μ = 0 := (mul_eq_zero.mp h7μ).resolve_left
          (by norm_num)
        exact Or.inr ⟨hv0, hμ0⟩
    have hs2raw : s₂.eval a =
        -(3840 : K) * (p.coeff 1).eval a * u.eval a * v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd2
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hs2kill : s₂.eval a = 0 := by
      rcases hdich with ⟨hu0, _⟩ | ⟨hv0, _⟩
      · rw [hs2raw, hu0]; ring
      · rw [hs2raw, hv0]; ring
    have hs3tie : s₃.eval a =
        -((10 : K) * μ₂ * u.eval a ^ 3) -
          (1344 : K) * μ * (p.coeff 1).eval a * u.eval a ^ 2 -
          (30720 : K) * (p.coeff 1).eval a ^ 2 * v.eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hd3
      simp only [Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot, zero_mul] at hev
      linear_combination -hev + (2 : K) * ((10 : K) * μ₂ * u.eval a +
        (1344 : K) * μ * (p.coeff 1).eval a) * hkilla
    have hq2raw : (131072 : K) * (q.coeff 2).eval a =
        s₄.eval a +
          (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
            u.eval a +
          (32768 : K) * κ * (p.coeff 0).eval a * (p.coeff 2).eval a +
          (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
          (64 : K) * κ₅ * (p.coeff 2).eval a -
          (768 : K) * κ₃ * (p.coeff 1).eval a * u.eval a +
          (7680 : K) * (p.coeff 0).eval a * v.eval a ^ 2 -
          (24 : K) * κ₃ * v.eval a ^ 2 := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq2red : (131072 : K) * (q.coeff 2).eval a =
        s₄.eval a +
          (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
            u.eval a +
          (8192 : K) * κ * (p.coeff 0).eval a * u.eval a ^ 2 +
          (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
          (16 : K) * κ₅ * u.eval a ^ 2 -
          (768 : K) * κ₃ * (p.coeff 1).eval a * u.eval a +
          (7680 : K) * (p.coeff 0).eval a * v.eval a ^ 2 -
          (24 : K) * κ₃ * v.eval a ^ 2 := by
      linear_combination hq2raw -
        ((8192 : K) * κ * (p.coeff 0).eval a - (16 : K) * κ₅) * hkilla
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, μ₂, κ₃, κ₅, h0, u, v, s₂, s₃, s₄, hh0, hHsq, hroot,
        hp3, hv, hd1, hp3d, hkilla, hnewtie, hdich, hs2raw, hs2kill,
        hs3tie, hq2raw, hq2red⟩⟩
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
    obtain ⟨f, hf, _hq4⟩ :=
      alignedNonsquareSixth_descent_410 hH hHdegree hsimple hcore6
    obtain ⟨κ₆, hM10rel⟩ :=
      alignedSeventhDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    obtain ⟨_hκ₆, hM100⟩ :=
      twentyFirstPower_nonsquareChamber_kill_410 hH hHdegree hnsq hM10rel
    obtain ⟨κ₇, hM12form⟩ :=
      alignedEighthDefectPowerRelation_410 hp hq hjac hH hp4' hq10'
        haligned hM
    have hcore8 :=
      alignedNonsquareEighth_core_410 hH hg hD0 hM4 hM60 hM8form hM100
        hM12form
    have hq2 := alignedNonsquareEighth_solved_410 hH hcore8 hf
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
    have hq2tie : (131072 : K) * (q.coeff 2).eval a =
        (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
            g.eval a +
          (32768 : K) * κ * (p.coeff 0).eval a * (p.coeff 2).eval a +
          (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
          (64 : K) * κ₅ * (p.coeff 2).eval a -
          (768 : K) * κ₃ * (p.coeff 1).eval a * g.eval a -
          (20 : K) * f.eval a ^ 3 *
            ((9 : K) * g.eval a ^ 2 - (4 : K) * (p.coeff 2).eval a) -
          (3840 : K) * (p.coeff 1).eval a * g.eval a * f.eval a ^ 2 -
          (30720 : K) * (p.coeff 1).eval a ^ 2 * f.eval a := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq2
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq2tie' : (131072 : K) * (q.coeff 2).eval a =
        (245760 : K) * (p.coeff 0).eval a * (p.coeff 1).eval a *
            g.eval a +
          (8192 : K) * κ * (p.coeff 0).eval a * g.eval a ^ 2 +
          (16384 : K) * κ * (p.coeff 1).eval a ^ 2 -
          (16 : K) * κ₅ * g.eval a ^ 2 -
          (768 : K) * κ₃ * (p.coeff 1).eval a * g.eval a -
          (160 : K) * f.eval a ^ 3 * g.eval a ^ 2 -
          (3840 : K) * (p.coeff 1).eval a * g.eval a * f.eval a ^ 2 -
          (30720 : K) * (p.coeff 1).eval a ^ 2 * f.eval a := by
      linear_combination hq2tie -
        ((8192 : K) * κ * (p.coeff 0).eval a - (16 : K) * κ₅ +
          (20 : K) * f.eval a ^ 3) * hkilla
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, κ₃, κ₅, g, f, hg, hf, hkilla, hq2tie, hq2tie'⟩⟩

#print axioms alignedEighthCoefficientJacobianRow_410
#print axioms alignedEighthDefect_weightedDerivative_identity_410
#print axioms alignedEighthDefectRow_eq_zero_410
#print axioms twelfthPowerRelation_of_weightTwelveRow_410
#print axioms alignedEighthDefectPowerRelation_410
#print axioms alignedSquareEighth_core_410
#print axioms alignedSquareEighth_solved_410
#print axioms alignedNonsquareEighth_core_410
#print axioms alignedNonsquareEighth_solved_410
#print axioms normalized410ScaleTwo_alignedEighthRow_packet
#print axioms normalized410ScaleTwo_alignedEighthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedEighthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedEighthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedEighthRow_rootData

end Max11DegreeRoutes
