import Fable410ScaleTwoAlignedFifthFaceScratch

/-! # Sixth aligned face for the normalized `(4,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable410ScaleTwoAlignedFifthFaceScratch` consumed the degree-`7`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the weight-`9`
first integral `M₈ = κ₅ H⁹` of the sixth defect, the perfect-cube core
`-10 (w² - 4 p₂)³`, the divisibilities `u² - 4 p₂ = h₀ v` resp.
`g² - 4 p₂ = H f`, and the solved quartic coefficient `q₄`.  This file
consumes the next unused aligned row, the degree-`6` Jacobian
coefficient — the first row that sees `q₃` — derived here directly from
the literal Keller bracket.

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` through degree-`7` brackets of `M₂`, `M₄`,
`M₆`, and `M₈`, the degree-`6` row is the weighted derivative of the
cleared seventh defect

`M₁₀ = 122880 p₀ p₁ H¹⁰ - 32768 q₃ H⁹ + 61440 p₀ p₂ p₃ H⁸
  + 30720 p₁² p₃ H⁸ + 30720 p₁ p₂² H⁸ - 5120 p₀ p₃³ H⁶
  - 15360 p₁ p₂ p₃² H⁶ - 5120 p₂³ p₃ H⁶ + 1920 p₁ p₃⁴ H⁴
  + 3840 p₂² p₃³ H⁴ - 960 p₂ p₃⁵ H² + 80 p₃⁷
  + κ (8192 p₀ p₃ H⁹ + 8192 p₁ p₂ H⁹)
  - 16 p₃ M₈ - (80 p₂ H² + 10 p₃²) M₆
  - (384 p₁ H⁴ + 192 p₂ p₃ H² - 16 p₃³) M₄
  - (3584 p₀ H⁶ + 2688 p₁ p₃ H⁴ + 1344 p₂² H⁴ - 336 p₂ p₃² H²
    + 35 p₃⁴) M₂`,

kept in factored form through the previous defects — the `M₂`-cofactor
is the first aligned defect cofactor that sees `p₀` — via the exact
multiplier identity

`16384 H⁸ · row₆[p₄ = H²] = (2 H M₁₀' - 21 M₁₀ H')
  + 56 p₃ (H M₈' - 9 M₈ H')
  + (112 p₂ H² + 70 p₃²) (2 H M₆' - 15 M₆ H')
  + (896 p₁ H⁴ + 1344 p₂ p₃ H² + 112 p₃³) (H M₄' - 6 M₄ H')
  + (3584 p₀ H⁶ + 6272 p₁ p₃ H⁴ + 3136 p₂² H⁴ + 2352 p₂ p₃² H²
    - 49 p₃⁴) (2 H M₂' - 9 M₂ H')`.

The correction module is EMPTY: the identity carries neither the
aligned-face residual `N` nor the degree-`11` relation `R` — the first
aligned row whose bracket combination is exact in the free letters.  On
the aligned face every previous bracket vanishes, so
`2 H M₁₀' = 21 M₁₀ H'` and the squared weight-`21/2` first integral

`M₁₀² = κ₆ H²¹`

holds for a preserved constant `κ₆` — the THIRD regeneration of the
odd-power discriminator shape (`M₂² = κ₂ H⁹`, `M₆² = κ₄ H¹⁵`,
`M₁₀² = κ₆ H²¹`).  The chambers then split honestly on parity:

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹` with `μ₃² = κ₆`:
  cancelling `h₀¹⁴` exposes the `h₀`-free core
  `80 u (u² - 4 p₂)³ + 1920 h₀² p₁ (u² - 4 p₂)²` — the previous face's
  perfect cube times `u` plus a `p₁`-loaded square correction.  On the
  consumed divisibility `u² - 4 p₂ = h₀ v` the whole core gains `h₀³`,
  and one further linear descent forces the NEW divisibility
  `80 u v³ - μ (35 u⁴ - 336 p₂ u² + 1344 p₂²) = h₀ s` — the first
  aligned constraint linking the descent letters `u`, `v` to the square
  residual `μ` — and solves the cubic-row letter with no `h₀` factor:
  `32768 q₃ = s + 61440 p₀ p₂ u + 30720 p₁² u - 5120 p₀ u³
  + 1920 p₁ v² + 8192 κ p₁ p₂ + κ₃ (16 u³ - 192 p₂ u)
  - h₀ (μ₂ (10 u² + 80 p₂) + 2688 μ p₁ u)
  - h₀² (16 κ₅ u + 384 κ₃ p₁ - 122880 p₀ p₁ - 8192 κ p₀ u)
  - h₀³ (μ₃ + 3584 μ p₀)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`, `M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹`: the odd
  exponent forces the parity kill `κ₆ = 0` and `M₁₀ ≡ 0`.  Cancelling
  `H⁷` exposes the same core in `g`, and the consumed divisibility
  `g² - 4 p₂ = H f` solves the cubic row OUTRIGHT — no new letter and
  no new divisibility:
  `32768 q₃ = 61440 p₀ p₂ g + 30720 p₁² g - 5120 p₀ g³ + 8192 κ p₁ p₂
  - κ₃ (192 p₂ g - 16 g³) + H (80 g f³ + 1920 p₁ f² + 122880 p₀ p₁
  + 8192 κ p₀ g - 16 κ₅ g - 384 κ₃ p₁)`.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the previous face, `w = u` or `g`): the square
chamber gains the `μ`-tie `80 u(a) v(a)³ = μ (35 u⁴ - 336 p₂ u²
+ 1344 p₂²)(a)`, collapsing on the quadratic kill to the product kill
`u(a) (16 v(a)³ - 7 μ u(a)³) = 0` — the first root tie between the two
square descent letters and `μ` — plus the `q₃` value tie carrying
`s(a)`; the nonsquare chamber gains the closed value tie
`32768 q₃(a) = 61440 p₀ p₂ g + 30720 p₁² g - 5120 p₀ g³ + 8192 κ p₁ p₂
- κ₃ (192 p₂ g - 16 g³)` at `a`, reducing on the kill to
`1024 q₃(a) = 320 p₀ g³ + 960 p₁² g + 64 κ p₁ g² - κ₃ g³` — the first
aligned value tie that sees `κ₃` at the root.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`, `dvd_of_sq_dvd_sq_poly`,
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, and the fifth-face divisibilities
`u² - 4 p₂ = h₀ v`, `g² - 4 p₂ = H f`.  The weight-`21/2` Wronskian
quotient `twentyFirstPowerRelation_of_weightTwentyOneHalfRow_410` is
new but generic.

No closure is claimed.  Both chambers remain open, the zero branches
(`u = 0`, `g = 0`, `v = 0`, `f = 0`, `s = 0`, `μ = 0`, `μ₂ = 0`,
`μ₃ = 0`, `κ = 0`, `κ₂ = 0`, `κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`)
are not excluded, and the constants are preserved where not previously
forced.  `p₀, p₁, p₂` are constrained only through the solved forms and
the divisibilities.  The next unused Keller row on the aligned face is
the degree-`5` Jacobian coefficient, the first row that sees `q₂`.  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`6` Keller coefficient on the aligned face -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`6` Jacobian coefficient, the first
aligned row that sees `q₃`.  It is derived directly from the Keller
bracket. -/
theorem alignedSeventhCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} :
        Finset (ℕ × ℕ)) := by decide
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC2]
  linear_combination hcoeff

/-! ## Aligned seventh defect -/

/-- Cleared seventh defect of the degree-`6` aligned `(4,10)` row, kept
in factored form through the third through sixth defects `M₂`, `M₄`,
`M₆`, and `M₈`:
`M₁₀ = 122880 p₀ p₁ H¹⁰ - 32768 q₃ H⁹ + 61440 p₀ p₂ p₃ H⁸
+ 30720 p₁² p₃ H⁸ + 30720 p₁ p₂² H⁸ - 5120 p₀ p₃³ H⁶
- 15360 p₁ p₂ p₃² H⁶ - 5120 p₂³ p₃ H⁶ + 1920 p₁ p₃⁴ H⁴
+ 3840 p₂² p₃³ H⁴ - 960 p₂ p₃⁵ H² + 80 p₃⁷
+ κ (8192 p₀ p₃ H⁹ + 8192 p₁ p₂ H⁹) - 16 p₃ M₈
- (80 p₂ H² + 10 p₃²) M₆ - (384 p₁ H⁴ + 192 p₂ p₃ H² - 16 p₃³) M₄
- (3584 p₀ H⁶ + 2688 p₁ p₃ H⁴ + 1344 p₂² H⁴ - 336 p₂ p₃² H²
+ 35 p₃⁴) M₂`.  Every monomial has exact `H`-weight `21/2`; the
`M₂`-cofactor is the first aligned defect cofactor seeing `p₀`. -/
def alignedSeventhDefect410 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (122880 : K[X]) * a0 * a1 * H ^ 10 - (32768 : K[X]) * b3 * H ^ 9 +
    (61440 : K[X]) * a0 * a2 * a3 * H ^ 8 +
    (30720 : K[X]) * a1 ^ 2 * a3 * H ^ 8 +
    (30720 : K[X]) * a1 * a2 ^ 2 * H ^ 8 -
    (5120 : K[X]) * a0 * a3 ^ 3 * H ^ 6 -
    (15360 : K[X]) * a1 * a2 * a3 ^ 2 * H ^ 6 -
    (5120 : K[X]) * a2 ^ 3 * a3 * H ^ 6 +
    (1920 : K[X]) * a1 * a3 ^ 4 * H ^ 4 +
    (3840 : K[X]) * a2 ^ 2 * a3 ^ 3 * H ^ 4 -
    (960 : K[X]) * a2 * a3 ^ 5 * H ^ 2 + (80 : K[X]) * a3 ^ 7 +
    Polynomial.C κ *
      ((8192 : K[X]) * a0 * a3 * H ^ 9 +
        (8192 : K[X]) * a1 * a2 * H ^ 9) -
    (16 : K[X]) * a3 * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ -
    ((80 : K[X]) * a2 * H ^ 2 + (10 : K[X]) * a3 ^ 2) *
      alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ -
    ((384 : K[X]) * a1 * H ^ 4 + (192 : K[X]) * a2 * a3 * H ^ 2 -
      (16 : K[X]) * a3 ^ 3) *
      alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ -
    ((3584 : K[X]) * a0 * H ^ 6 + (2688 : K[X]) * a1 * a3 * H ^ 4 +
      (1344 : K[X]) * a2 ^ 2 * H ^ 4 - (336 : K[X]) * a2 * a3 ^ 2 * H ^ 2 +
      (35 : K[X]) * a3 ^ 4) * alignedThirdDefect410 H a1 a2 a3 b7 κ

set_option maxHeartbeats 400000000 in
/-- Exact combination of the degree-`6` Jacobian expression with the
weight-`21/2` bracket of `M₁₀`.  The only corrections are the consumed
degree-`10` through degree-`7` brackets of `M₂`, `M₄`, `M₆`, and `M₈`:
neither the aligned-face residual `N` nor the degree-`11` relation `R`
appears at all — the correction module is empty.  Every correction
vanishes on the aligned face. -/
theorem alignedSeventhDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (16384 : K[X]) * H ^ 8 *
        ((H ^ 2).derivative * (b3 * (3 : K[X])) +
          a3.derivative * (b4 * (4 : K[X])) +
          a2.derivative * (b5 * (5 : K[X])) +
          a1.derivative * (b6 * (6 : K[X])) +
          a0.derivative * (b7 * (7 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b3.derivative +
          (a3 * (3 : K[X])) * b4.derivative +
          (a2 * (2 : K[X])) * b5.derivative +
          a1 * b6.derivative)) =
      ((2 : K[X]) * H *
          (alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7
            κ).derivative -
        (21 : K[X]) *
          alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (56 : K[X]) * a3 *
          (H * (alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7
              κ).derivative -
            (9 : K[X]) * alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ *
              H.derivative) +
        ((112 : K[X]) * a2 * H ^ 2 + (70 : K[X]) * a3 ^ 2) *
          ((2 : K[X]) * H *
              (alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ).derivative -
            (15 : K[X]) * alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ *
              H.derivative) +
        ((896 : K[X]) * a1 * H ^ 4 + (1344 : K[X]) * a2 * a3 * H ^ 2 +
            (112 : K[X]) * a3 ^ 3) *
          (H * (alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ).derivative -
            (6 : K[X]) * alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ *
              H.derivative) +
        ((3584 : K[X]) * a0 * H ^ 6 + (6272 : K[X]) * a1 * a3 * H ^ 4 +
            (3136 : K[X]) * a2 ^ 2 * H ^ 4 +
            (2352 : K[X]) * a2 * a3 ^ 2 * H ^ 2 -
            (49 : K[X]) * a3 ^ 4) *
          ((2 : K[X]) * H *
              (alignedThirdDefect410 H a1 a2 a3 b7 κ).derivative -
            (9 : K[X]) * alignedThirdDefect410 H a1 a2 a3 b7 κ *
              H.derivative) := by
  simp only [alignedSeventhDefect410, alignedSixthDefect410,
    alignedFifthDefect410, alignedFourthDefect410, alignedThirdDefect410,
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
degree-`7` rows, the degree-`6` row is the weighted derivative
`2 H M₁₀' - 21 M₁₀ H' = 0`. -/
theorem alignedSeventhDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    (2 : K[X]) * H *
        (alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ).derivative -
      (21 : K[X]) *
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedSeventhCoefficientJacobianRow_410 hp hq hjac
  rw [hp4] at hrow
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC3, hC4, hC5, hC6, hC7, hC2] at hrow
  have hB2 :=
    alignedThirdDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB4 :=
    alignedFourthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB6 :=
    alignedFifthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hB8 :=
    alignedSixthDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM
  have hid := alignedSeventhDefect_weightedDerivative_identity_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hB2, hB4, hB6, hB8] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-! ## Squared weight-`21/2` polynomial first integral -/

/-- Generic Wronskian quotient for the weight-`21/2` bracket: over a
characteristic-zero field, `2 H D' - 21 D H' = 0` forces
`D² = C c * H²¹`. -/
theorem twentyFirstPowerRelation_of_weightTwentyOneHalfRow_410 {K : Type*}
    [Field K] [CharZero K] {H D : K[X]} (hH : H ≠ 0)
    (hrow : (2 : K[X]) * H * D.derivative -
      (21 : K[X]) * D * H.derivative = 0) :
    ∃ c : K, D ^ 2 = Polynomial.C c * H ^ 21 := by
  have hrowC :
      Polynomial.C (2 : K) * H * D.derivative -
          Polynomial.C (21 : K) * D * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC21 : Polynomial.C (21 : K) = (21 : K[X]) :=
      Polynomial.C_eq_natCast 21
    rw [hC2, hC21]
    exact hrow
  have hW : Polynomial.wronskian (D ^ 2) (H ^ 21) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      D ^ 2 * (Polynomial.C (21 : K) * H ^ (21 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * D ^ (2 - 1) * D.derivative) * H ^ 21 =
          D * H ^ 20 *
            (Polynomial.C (21 : K) * D * H.derivative -
              Polynomial.C (2 : K) * H * D.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 21 hH) hW

/-- Squared weight-`21/2` polynomial first integral of the aligned
`(4,10)` seventh defect: `M₁₀² = κ₆ H²¹` — the odd-power discriminator
shape regenerated a THIRD time, one level below the even weight-`9`
shape of the degree-`7` row. -/
theorem alignedSeventhDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₆ : K,
      alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₆ * H ^ 21 :=
  twentyFirstPowerRelation_of_weightTwentyOneHalfRow_410 hH
    (alignedSeventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

/-! ## Chamber quotients of the twenty-first-power relation -/

/-- In the square chamber `H = h₀²` the twenty-first-power relation
resolves to the literal half-integral form `D = C μ₃ * h₀²¹` with
`μ₃² = c`; the scalar `μ₃` is an honest residual and is not cleared. -/
theorem twentyFirstPower_squareChamber_form_410 {K : Type*}
    [Field K] [CharZero K] {H h0 D : K[X]} {c : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 21) :
    ∃ μ₃ : K, μ₃ ^ 2 = c ∧ D = Polynomial.C μ₃ * h0 ^ 21 := by
  have hdvd : (h0 ^ 21) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c, ?_⟩
    rw [hrel, hHsq]
    ring
  obtain ⟨F, hF⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hF2 : F ^ 2 = Polynomial.C c := by
    have h42 := hrel
    rw [hF, hHsq] at h42
    apply mul_left_cancel₀ (pow_ne_zero 42 hh0)
    linear_combination h42
  have hFdeg : F.natDegree = 0 := by
    have h2 : (F ^ 2).natDegree = 0 := by
      rw [hF2]
      exact Polynomial.natDegree_C c
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₃, hμ₃⟩ := Polynomial.natDegree_eq_zero.mp hFdeg
  refine ⟨μ₃, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₃ ^ 2) = Polynomial.C c := by
      rw [Polynomial.C_pow, hμ₃, hF2]
    exact Polynomial.C_injective hCμ
  · rw [hF, ← hμ₃]
    ring

/-- Parity kill in the nonsquare chamber: the odd exponent of the
twenty-first-power relation forces its constant to vanish, and with it
the whole seventh defect. -/
theorem twentyFirstPower_nonsquareChamber_kill_410 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H D : K[X]} {c : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hrel : D ^ 2 = Polynomial.C c * H ^ 21) : c = 0 ∧ D = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hdvd : (H ^ 10) ^ 2 ∣ D ^ 2 := by
    refine ⟨Polynomial.C c * H, ?_⟩
    rw [hrel]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C c * H := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hH)
    have h20 := hrel
    rw [hG] at h20
    linear_combination h20
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C c := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hc : c = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [ha, zero_mul] at hev
    exact hev.symm
  refine ⟨hc, ?_⟩
  have hzero : D ^ 2 = 0 := by
    rw [hrel, hc, Polynomial.C_0, zero_mul]
  exact sq_eq_zero_iff.mp hzero

/-! ## Square chamber -/

/-- Cleared square-core form of the seventh defect relation: cancelling
`h₀¹⁴` from `M₁₀ = μ₃ h₀²¹` on `p₃ = h₀² u`, `M₂ = μ h₀⁹`,
`M₄ = κ₃ H⁶`, `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹` exposes the `h₀`-free core
`80 u (u² - 4 p₂)³ + 1920 h₀² p₁ (u² - 4 p₂)²` — the previous face's
perfect cube times `u` plus a `p₁`-loaded square correction — carried
by `h₀³` against the explicit quotient. -/
theorem alignedSquareSeventh_core_410 {K : Type*} [Field K] [CharZero K]
    {H h0 u a0 a1 a2 a3 b3 b4 b5 b6 b7 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ : K}
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
      Polynomial.C μ₃ * h0 ^ 21) :
    (80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (1920 : K[X]) * h0 ^ 2 * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
      h0 ^ 3 *
        (Polynomial.C μ *
            ((35 : K[X]) * u ^ 4 - (336 : K[X]) * a2 * u ^ 2 +
              (1344 : K[X]) * a2 ^ 2) +
          h0 * ((32768 : K[X]) * b3 - (61440 : K[X]) * a0 * a2 * u -
            (30720 : K[X]) * a1 ^ 2 * u + (5120 : K[X]) * a0 * u ^ 3 -
            Polynomial.C κ * ((8192 : K[X]) * a1 * a2) -
            Polynomial.C κ₃ *
              ((16 : K[X]) * u ^ 3 - (192 : K[X]) * a2 * u)) +
          h0 ^ 2 * (Polynomial.C μ₂ *
              ((10 : K[X]) * u ^ 2 + (80 : K[X]) * a2) +
            Polynomial.C μ * ((2688 : K[X]) * a1 * u)) +
          h0 ^ 3 * (Polynomial.C κ₅ * ((16 : K[X]) * u) +
            Polynomial.C κ₃ * ((384 : K[X]) * a1) -
            (122880 : K[X]) * a0 * a1 -
            Polynomial.C κ * ((8192 : K[X]) * a0 * u)) +
          h0 ^ 4 * (Polynomial.C μ₃ +
            Polynomial.C μ * ((3584 : K[X]) * a0))) := by
  have hM10' := hM10
  simp only [alignedSeventhDefect410] at hM10'
  rw [hM2, hM4, hM6, hM8, hHsq, hp3] at hM10'
  apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
  linear_combination hM10'

/-- The consumed degree-`6` row in the square chamber: on the
divisibility `u² - 4 p₂ = h₀ v` of the previous face the core gains
`h₀³`, and one further linear descent forces the NEW divisibility
`80 u v³ - μ (35 u⁴ - 336 p₂ u² + 1344 p₂²) = h₀ s` — the first
aligned constraint linking `u`, `v` to the square residual `μ` — and
solves the cubic row against the preserved constants.  The new letter
`q₃` carries no `h₀` factor. -/
theorem alignedSquareSeventh_solved_410 {K : Type*} [Field K] [CharZero K]
    {h0 u v a0 a1 a2 b3 : K[X]} {κ μ κ₃ μ₂ κ₅ μ₃ : K}
    (hh0 : h0 ≠ 0)
    (hcore :
      (80 : K[X]) * u * (u ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (1920 : K[X]) * h0 ^ 2 * a1 * (u ^ 2 - (4 : K[X]) * a2) ^ 2 =
        h0 ^ 3 *
          (Polynomial.C μ *
              ((35 : K[X]) * u ^ 4 - (336 : K[X]) * a2 * u ^ 2 +
                (1344 : K[X]) * a2 ^ 2) +
            h0 * ((32768 : K[X]) * b3 - (61440 : K[X]) * a0 * a2 * u -
              (30720 : K[X]) * a1 ^ 2 * u + (5120 : K[X]) * a0 * u ^ 3 -
              Polynomial.C κ * ((8192 : K[X]) * a1 * a2) -
              Polynomial.C κ₃ *
                ((16 : K[X]) * u ^ 3 - (192 : K[X]) * a2 * u)) +
            h0 ^ 2 * (Polynomial.C μ₂ *
                ((10 : K[X]) * u ^ 2 + (80 : K[X]) * a2) +
              Polynomial.C μ * ((2688 : K[X]) * a1 * u)) +
            h0 ^ 3 * (Polynomial.C κ₅ * ((16 : K[X]) * u) +
              Polynomial.C κ₃ * ((384 : K[X]) * a1) -
              (122880 : K[X]) * a0 * a1 -
              Polynomial.C κ * ((8192 : K[X]) * a0 * u)) +
            h0 ^ 4 * (Polynomial.C μ₃ +
              Polynomial.C μ * ((3584 : K[X]) * a0))))
    (hv : u ^ 2 - (4 : K[X]) * a2 = h0 * v) :
    ∃ s : K[X],
      (80 : K[X]) * u * v ^ 3 -
          Polynomial.C μ *
            ((35 : K[X]) * u ^ 4 - (336 : K[X]) * a2 * u ^ 2 +
              (1344 : K[X]) * a2 ^ 2) = h0 * s ∧
      (32768 : K[X]) * b3 =
        s + (61440 : K[X]) * a0 * a2 * u + (30720 : K[X]) * a1 ^ 2 * u -
          (5120 : K[X]) * a0 * u ^ 3 + (1920 : K[X]) * a1 * v ^ 2 +
          Polynomial.C κ * ((8192 : K[X]) * a1 * a2) +
          Polynomial.C κ₃ *
            ((16 : K[X]) * u ^ 3 - (192 : K[X]) * a2 * u) -
          h0 * (Polynomial.C μ₂ *
              ((10 : K[X]) * u ^ 2 + (80 : K[X]) * a2) +
            Polynomial.C μ * ((2688 : K[X]) * a1 * u)) -
          h0 ^ 2 * (Polynomial.C κ₅ * ((16 : K[X]) * u) +
            Polynomial.C κ₃ * ((384 : K[X]) * a1) -
            (122880 : K[X]) * a0 * a1 -
            Polynomial.C κ * ((8192 : K[X]) * a0 * u)) -
          h0 ^ 3 * (Polynomial.C μ₃ +
            Polynomial.C μ * ((3584 : K[X]) * a0)) := by
  refine ⟨(32768 : K[X]) * b3 - (61440 : K[X]) * a0 * a2 * u -
      (30720 : K[X]) * a1 ^ 2 * u + (5120 : K[X]) * a0 * u ^ 3 -
      (1920 : K[X]) * a1 * v ^ 2 -
      Polynomial.C κ * ((8192 : K[X]) * a1 * a2) -
      Polynomial.C κ₃ * ((16 : K[X]) * u ^ 3 - (192 : K[X]) * a2 * u) +
      h0 * (Polynomial.C μ₂ * ((10 : K[X]) * u ^ 2 + (80 : K[X]) * a2) +
        Polynomial.C μ * ((2688 : K[X]) * a1 * u)) +
      h0 ^ 2 * (Polynomial.C κ₅ * ((16 : K[X]) * u) +
        Polynomial.C κ₃ * ((384 : K[X]) * a1) -
        (122880 : K[X]) * a0 * a1 -
        Polynomial.C κ * ((8192 : K[X]) * a0 * u)) +
      h0 ^ 3 * (Polynomial.C μ₃ +
        Polynomial.C μ * ((3584 : K[X]) * a0)), ?_, ?_⟩
  · rw [hv] at hcore
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    linear_combination hcore
  · ring

/-! ## Nonsquare chamber -/

/-- Cleared nonsquare-core form of the seventh defect relation:
cancelling `H⁷` from the parity-killed `M₁₀ = 0` on `p₃ = H g`,
`M₂ = 0`, `M₄ = κ₃ H⁶`, `M₆ = 0`, `M₈ = κ₅ H⁹` exposes the same core
`80 g (g² - 4 p₂)³ + 1920 H p₁ (g² - 4 p₂)²` carried by `H²` against
the explicit quotient. -/
theorem alignedNonsquareSeventh_core_410 {K : Type*}
    [Field K] [CharZero K]
    {H g a0 a1 a2 a3 b3 b4 b5 b6 b7 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0) (hg : a3 = H * g)
    (hM20 : alignedThirdDefect410 H a1 a2 a3 b7 κ = 0)
    (hM4 : alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 6)
    (hM60 : alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ = 0)
    (hM8 : alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 9)
    (hM100 : alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ = 0) :
    (80 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
        (1920 : K[X]) * H * a1 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
      H ^ 2 *
        ((32768 : K[X]) * b3 - (61440 : K[X]) * a0 * a2 * g -
          (30720 : K[X]) * a1 ^ 2 * g + (5120 : K[X]) * a0 * g ^ 3 -
          Polynomial.C κ * ((8192 : K[X]) * a1 * a2) -
          Polynomial.C κ₃ *
            ((16 : K[X]) * g ^ 3 - (192 : K[X]) * a2 * g) +
          H * (Polynomial.C κ₅ * ((16 : K[X]) * g) +
            Polynomial.C κ₃ * ((384 : K[X]) * a1) -
            (122880 : K[X]) * a0 * a1 -
            Polynomial.C κ * ((8192 : K[X]) * a0 * g))) := by
  have hM100' := hM100
  simp only [alignedSeventhDefect410] at hM100'
  rw [hM20, hM4, hM60, hM8, hg] at hM100'
  apply mul_left_cancel₀ (pow_ne_zero 7 hH)
  linear_combination hM100'

/-- The consumed degree-`6` row in the nonsquare chamber: on the
divisibility `g² - 4 p₂ = H f` of the previous face the cubic row is
solved OUTRIGHT — no new letter, no new divisibility, and `q₃` carries
no `H` factor. -/
theorem alignedNonsquareSeventh_solved_410 {K : Type*}
    [Field K] [CharZero K]
    {H g f a0 a1 a2 b3 : K[X]} {κ κ₃ κ₅ : K}
    (hH : H ≠ 0)
    (hcore :
      (80 : K[X]) * g * (g ^ 2 - (4 : K[X]) * a2) ^ 3 +
          (1920 : K[X]) * H * a1 * (g ^ 2 - (4 : K[X]) * a2) ^ 2 =
        H ^ 2 *
          ((32768 : K[X]) * b3 - (61440 : K[X]) * a0 * a2 * g -
            (30720 : K[X]) * a1 ^ 2 * g + (5120 : K[X]) * a0 * g ^ 3 -
            Polynomial.C κ * ((8192 : K[X]) * a1 * a2) -
            Polynomial.C κ₃ *
              ((16 : K[X]) * g ^ 3 - (192 : K[X]) * a2 * g) +
            H * (Polynomial.C κ₅ * ((16 : K[X]) * g) +
              Polynomial.C κ₃ * ((384 : K[X]) * a1) -
              (122880 : K[X]) * a0 * a1 -
              Polynomial.C κ * ((8192 : K[X]) * a0 * g))))
    (hf : g ^ 2 - (4 : K[X]) * a2 = H * f) :
    (32768 : K[X]) * b3 =
      (61440 : K[X]) * a0 * a2 * g + (30720 : K[X]) * a1 ^ 2 * g -
        (5120 : K[X]) * a0 * g ^ 3 +
        Polynomial.C κ * ((8192 : K[X]) * a1 * a2) +
        Polynomial.C κ₃ * ((16 : K[X]) * g ^ 3 - (192 : K[X]) * a2 * g) +
        H * ((80 : K[X]) * g * f ^ 3 + (1920 : K[X]) * a1 * f ^ 2 +
          (122880 : K[X]) * a0 * a1 +
          Polynomial.C κ * ((8192 : K[X]) * a0 * g) -
          Polynomial.C κ₅ * ((16 : K[X]) * g) -
          Polynomial.C κ₃ * ((384 : K[X]) * a1)) := by
  rw [hf] at hcore
  apply mul_left_cancel₀ (pow_ne_zero 2 hH)
  linear_combination -hcore

/-! ## Source-facing seventh-row packets -/

/-- Source-facing squared weight-`21/2` integral of a normalized aligned
scale-two `(4,10)` source: the degree-`6` row is consumed into
`M₁₀² = κ₆ H²¹` on top of the previous aligned packet, together with
the chamber-free root jet of the previous rows. -/
theorem normalized410ScaleTwo_alignedSeventhRow_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ κ₂ κ₃ κ₄ κ₅ κ₆ : K,
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
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM, hrel, hM4, hM6, hM8, hM10,
    fun a ha =>
      ⟨alignedThird_rootKill_p3_410 hrel ha,
        alignedThird_q8_secondOrderKill_410 hM hrel ha⟩⟩

/-- Exact square-chamber seventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the
half-integral form `M₁₀ = μ₃ h₀²¹`, the NEW divisibility
`80 u v³ - μ (35 u⁴ - 336 p₂ u² + 1344 p₂²) = h₀ s`, and the solved
cubic row.  The constants `μ`, `κ₃`, `μ₂`, `κ₅`, and `μ₃` are
preserved, not cleared, and `q₃` carries no `h₀` factor. -/
theorem normalized410ScaleTwo_alignedSeventhRow_squareChamber_packet
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
    ∃ (κ μ κ₃ μ₂ κ₅ μ₃ : K) (u v s : K[X]),
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
        u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
        (80 : K[X]) * u * v ^ 3 -
            Polynomial.C μ *
              ((35 : K[X]) * u ^ 4 - (336 : K[X]) * p.coeff 2 * u ^ 2 +
                (1344 : K[X]) * p.coeff 2 ^ 2) = h0 * s ∧
        (32768 : K[X]) * q.coeff 3 =
          s + (61440 : K[X]) * p.coeff 0 * p.coeff 2 * u +
            (30720 : K[X]) * p.coeff 1 ^ 2 * u -
            (5120 : K[X]) * p.coeff 0 * u ^ 3 +
            (1920 : K[X]) * p.coeff 1 * v ^ 2 +
            Polynomial.C κ * ((8192 : K[X]) * p.coeff 1 * p.coeff 2) +
            Polynomial.C κ₃ *
              ((16 : K[X]) * u ^ 3 - (192 : K[X]) * p.coeff 2 * u) -
            h0 * (Polynomial.C μ₂ *
                ((10 : K[X]) * u ^ 2 + (80 : K[X]) * p.coeff 2) +
              Polynomial.C μ * ((2688 : K[X]) * p.coeff 1 * u)) -
            h0 ^ 2 * (Polynomial.C κ₅ * ((16 : K[X]) * u) +
              Polynomial.C κ₃ * ((384 : K[X]) * p.coeff 1) -
              (122880 : K[X]) * p.coeff 0 * p.coeff 1 -
              Polynomial.C κ * ((8192 : K[X]) * p.coeff 0 * u)) -
            h0 ^ 3 * (Polynomial.C μ₃ +
              Polynomial.C μ * ((3584 : K[X]) * p.coeff 0)) := by
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
  have hcore7 :=
    alignedSquareSeventh_core_410 hh0 hHsq hp3 hDform hM4 hM6form
      hM8form hM10form
  obtain ⟨s, hs, hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
  exact ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, u, v, s, hp3, hDform, hM4, hM6form,
    hM8form, hM10form, hv, hs, hq3⟩

/-- Exact nonsquare-chamber seventh packet of a normalized aligned
scale-two `(4,10)` source: the identifying chamber data, the parity
kill `M₁₀ ≡ 0` (forced `κ₆ = 0`), and the cubic row solved OUTRIGHT on
the previous face's divisibility `g² - 4 p₂ = H f` — no new letter and
no new divisibility.  `q₃` carries no `H` factor. -/
theorem normalized410ScaleTwo_alignedSeventhRow_nonsquareChamber_packet
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
        alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 ∧
        g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
        (32768 : K[X]) * q.coeff 3 =
          (61440 : K[X]) * p.coeff 0 * p.coeff 2 * g +
            (30720 : K[X]) * p.coeff 1 ^ 2 * g -
            (5120 : K[X]) * p.coeff 0 * g ^ 3 +
            Polynomial.C κ * ((8192 : K[X]) * p.coeff 1 * p.coeff 2) +
            Polynomial.C κ₃ *
              ((16 : K[X]) * g ^ 3 - (192 : K[X]) * p.coeff 2 * g) +
            H * ((80 : K[X]) * g * f ^ 3 +
              (1920 : K[X]) * p.coeff 1 * f ^ 2 +
              (122880 : K[X]) * p.coeff 0 * p.coeff 1 +
              Polynomial.C κ * ((8192 : K[X]) * p.coeff 0 * g) -
              Polynomial.C κ₅ * ((16 : K[X]) * g) -
              Polynomial.C κ₃ * ((384 : K[X]) * p.coeff 1)) := by
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
  have hcore7 :=
    alignedNonsquareSeventh_core_410 hH hg hD0 hM4 hM60 hM8form hM100
  have hq3 := alignedNonsquareSeventh_solved_410 hH hcore7 hf
  exact ⟨κ, κ₃, κ₅, g, f, hg, hD0, hM4, hM60, hM8form, hM100, hf, hq3⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`6`
aligned row: the square chamber carries the half-integral form
`M₁₀ = μ₃ h₀²¹`, the nonsquare chamber the parity kill `M₁₀ = 0`.
Neither chamber is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedSeventhRow_chamberDichotomy
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
      ∃ (κ μ₃ : K) (u : K[X]),
        p.coeff 3 = h0 ^ 2 * u ∧
          alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5)
              (q.coeff 6) (q.coeff 7) κ = Polynomial.C μ₃ * h0 ^ 21) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g : K[X]),
        p.coeff 3 = H * g ∧
          alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5)
              (q.coeff 6) (q.coeff 7) κ = 0) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized410ScaleTwo_alignedSeventhRow_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, μ₂, κ₅, μ₃, u, v, s, hp3, _hM2f, _hM4, _hM6f,
      _hM8, hM10, _hv, _hs, _hq3⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ₃, u, hp3, hM10⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized410ScaleTwo_alignedSeventhRow_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, g, f, hg, _hM20, _hM4, _hM60, _hM8, hM100, _hf,
      _hq3⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g, hg, hM100⟩

/-- Extended root data of the consumed degree-`6` row: at scale two the
common core has a root `a` where the previous jet dies (`p₃(a) = 0`,
`q₈` to second order — the deeper kills are in the previous root
packets), and the NEW degree-`6` content splits by chamber: the square
chamber gains the `μ`-tie `80 u(a) v(a)³ = μ (35 u⁴ - 336 p₂ u²
+ 1344 p₂²)(a)`, its collapse on the quadratic kill to the product kill
`u(a) (16 v(a)³ - 7 μ u(a)³) = 0`, and the `q₃` value tie carrying the
descent letter `s(a)`; the nonsquare chamber gains the closed value tie
`32768 q₃(a) = 61440 p₀ p₂ g + 30720 p₁² g - 5120 p₀ g³ + 8192 κ p₁ p₂
- κ₃ (192 p₂ g - 16 g³)` at `a` and its reduction
`1024 q₃(a) = 320 p₀ g³ + 960 p₁² g + 64 κ p₁ g² - κ₃ g³` — the first
aligned value tie seeing `κ₃` at the root.  `q₃` does NOT vanish and no
new vanishing is claimed. -/
theorem normalized410ScaleTwo_alignedSeventhRow_rootData
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
      ((∃ (μ κ₃ : K) (h0 u v s : K[X]), h0 ≠ 0 ∧ H = h0 ^ 2 ∧
          h0.eval a = 0 ∧
          p.coeff 3 = h0 ^ 2 * u ∧
          u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
          (80 : K[X]) * u * v ^ 3 -
              Polynomial.C μ *
                ((35 : K[X]) * u ^ 4 -
                  (336 : K[X]) * p.coeff 2 * u ^ 2 +
                  (1344 : K[X]) * p.coeff 2 ^ 2) = h0 * s ∧
          (p.coeff 3).derivative.eval a = 0 ∧
          u.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
          (80 : K) * u.eval a * v.eval a ^ 3 =
            μ * ((35 : K) * u.eval a ^ 4 -
              (336 : K) * (p.coeff 2).eval a * u.eval a ^ 2 +
              (1344 : K) * (p.coeff 2).eval a ^ 2) ∧
          u.eval a * ((16 : K) * v.eval a ^ 3 - (7 : K) * μ * u.eval a ^ 3) = 0 ∧
          (32768 : K) * (q.coeff 3).eval a =
            s.eval a +
              (61440 : K) * (p.coeff 0).eval a * (p.coeff 2).eval a *
                u.eval a +
              (30720 : K) * (p.coeff 1).eval a ^ 2 * u.eval a -
              (5120 : K) * (p.coeff 0).eval a * u.eval a ^ 3 +
              (1920 : K) * (p.coeff 1).eval a * v.eval a ^ 2 +
              (8192 : K) * κ * (p.coeff 1).eval a * (p.coeff 2).eval a +
              κ₃ * ((16 : K) * u.eval a ^ 3 -
                (192 : K) * (p.coeff 2).eval a * u.eval a) ∧
          (32768 : K) * (q.coeff 3).eval a =
            s.eval a +
              (10240 : K) * (p.coeff 0).eval a * u.eval a ^ 3 +
              (30720 : K) * (p.coeff 1).eval a ^ 2 * u.eval a +
              (2048 : K) * κ * (p.coeff 1).eval a * u.eval a ^ 2 +
              (1920 : K) * (p.coeff 1).eval a * v.eval a ^ 2 -
              (32 : K) * κ₃ * u.eval a ^ 3) ∨
        ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
          ∃ (κ₃ : K) (g f : K[X]), p.coeff 3 = H * g ∧
            g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f ∧
            g.eval a ^ 2 = (4 : K) * (p.coeff 2).eval a ∧
            (32768 : K) * (q.coeff 3).eval a =
              (61440 : K) * (p.coeff 0).eval a * (p.coeff 2).eval a *
                  g.eval a +
                (30720 : K) * (p.coeff 1).eval a ^ 2 * g.eval a -
                (5120 : K) * (p.coeff 0).eval a * g.eval a ^ 3 +
                (8192 : K) * κ * (p.coeff 1).eval a *
                  (p.coeff 2).eval a +
                κ₃ * ((16 : K) * g.eval a ^ 3 -
                  (192 : K) * (p.coeff 2).eval a * g.eval a) ∧
            (1024 : K) * (q.coeff 3).eval a =
              (320 : K) * (p.coeff 0).eval a * g.eval a ^ 3 +
                (960 : K) * (p.coeff 1).eval a ^ 2 * g.eval a +
                (64 : K) * κ * (p.coeff 1).eval a * g.eval a ^ 2 -
                κ₃ * g.eval a ^ 3)) := by
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
    obtain ⟨s, hs, hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore7 hv
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
    have hq3tie : (32768 : K) * (q.coeff 3).eval a =
        s.eval a +
          (61440 : K) * (p.coeff 0).eval a * (p.coeff 2).eval a *
            u.eval a +
          (30720 : K) * (p.coeff 1).eval a ^ 2 * u.eval a -
          (5120 : K) * (p.coeff 0).eval a * u.eval a ^ 3 +
          (1920 : K) * (p.coeff 1).eval a * v.eval a ^ 2 +
          (8192 : K) * κ * (p.coeff 1).eval a * (p.coeff 2).eval a +
          κ₃ * ((16 : K) * u.eval a ^ 3 -
            (192 : K) * (p.coeff 2).eval a * u.eval a) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq3tie' : (32768 : K) * (q.coeff 3).eval a =
        s.eval a +
          (10240 : K) * (p.coeff 0).eval a * u.eval a ^ 3 +
          (30720 : K) * (p.coeff 1).eval a ^ 2 * u.eval a +
          (2048 : K) * κ * (p.coeff 1).eval a * u.eval a ^ 2 +
          (1920 : K) * (p.coeff 1).eval a * v.eval a ^ 2 -
          (32 : K) * κ₃ * u.eval a ^ 3 := by
      linear_combination hq3tie +
        (-(15360 : K) * (p.coeff 0).eval a * u.eval a -
          (2048 : K) * κ * (p.coeff 1).eval a +
          (48 : K) * κ₃ * u.eval a) * hkilla
    exact ⟨a, κ, hHroot, hclear, hp3a, hq8d,
      Or.inl ⟨μ, κ₃, h0, u, v, s, hh0, hHsq, hroot, hp3, hv, hs, hp3d,
        hkilla, hμtie, hkilltie, hq3tie, hq3tie'⟩⟩
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
    have hcore7 :=
      alignedNonsquareSeventh_core_410 hH hg hD0 hM4 hM60 hM8form hM100
    have hq3 := alignedNonsquareSeventh_solved_410 hH hcore7 hf
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
    have hq3tie : (32768 : K) * (q.coeff 3).eval a =
        (61440 : K) * (p.coeff 0).eval a * (p.coeff 2).eval a *
            g.eval a +
          (30720 : K) * (p.coeff 1).eval a ^ 2 * g.eval a -
          (5120 : K) * (p.coeff 0).eval a * g.eval a ^ 3 +
          (8192 : K) * κ * (p.coeff 1).eval a * (p.coeff 2).eval a +
          κ₃ * ((16 : K) * g.eval a ^ 3 -
            (192 : K) * (p.coeff 2).eval a * g.eval a) := by
      have hev := congrArg (fun w : K[X] => w.eval a) hq3
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
        Polynomial.eval_C] at hev
      rw [hroot] at hev
      norm_num at hev
      linear_combination hev
    have hq3tie' : (1024 : K) * (q.coeff 3).eval a =
        (320 : K) * (p.coeff 0).eval a * g.eval a ^ 3 +
          (960 : K) * (p.coeff 1).eval a ^ 2 * g.eval a +
          (64 : K) * κ * (p.coeff 1).eval a * g.eval a ^ 2 -
          κ₃ * g.eval a ^ 3 := by
      linear_combination (1 / 32 : K) * hq3tie +
        ((-(480 : K)) * (p.coeff 0).eval a * g.eval a -
          (64 : K) * κ * (p.coeff 1).eval a +
          (3 / 2 : K) * κ₃ * g.eval a) * hkilla
    exact ⟨a, κ, hroot, hclear, hp3a, hq8d,
      Or.inr ⟨hnsq, κ₃, g, f, hg, hf, hkilla, hq3tie, hq3tie'⟩⟩

#print axioms alignedSeventhCoefficientJacobianRow_410
#print axioms alignedSeventhDefect_weightedDerivative_identity_410
#print axioms alignedSeventhDefectRow_eq_zero_410
#print axioms twentyFirstPowerRelation_of_weightTwentyOneHalfRow_410
#print axioms alignedSeventhDefectPowerRelation_410
#print axioms twentyFirstPower_squareChamber_form_410
#print axioms twentyFirstPower_nonsquareChamber_kill_410
#print axioms alignedSquareSeventh_core_410
#print axioms alignedSquareSeventh_solved_410
#print axioms alignedNonsquareSeventh_core_410
#print axioms alignedNonsquareSeventh_solved_410
#print axioms normalized410ScaleTwo_alignedSeventhRow_packet
#print axioms normalized410ScaleTwo_alignedSeventhRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedSeventhRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedSeventhRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedSeventhRow_rootData

end Max11DegreeRoutes
