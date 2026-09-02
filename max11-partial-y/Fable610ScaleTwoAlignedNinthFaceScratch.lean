import Fable610ScaleTwoAlignedEighthFaceScratch

/-! # Ninth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedEighthFaceScratch` consumed the degree-`7`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
chamber-free weight-twenty integral `J = κ₇ H²⁰`, with the
square-chamber product divisibility `w₁ (e₂ - 3 e₁ w₁) = h₀ u₂` and
the nonsquare-chamber divisor `81 p₂ + 3 g₁² t₁ - g₁ t₂ = H u` (the
first `p₂` constraint of the aligned tower) with `q₂` solved outright.
This file consumes the next unused aligned row, the degree-`6`
Jacobian coefficient — the first row that sees `q₁` (pairs
`(0,7), (1,6), (2,5), (3,4), (4,3), (5,2), (6,1)`).

At the source level, modulo the face and the consumed degree-`13`
through degree-`7` rows, the degree-`6` row is the weighted derivative
of the cleared ninth defect

`L = 1813985280 (p₀ p₃ + p₁ p₂) H²¹ - 1632586752 q₁ H²²
  - 604661760 (p₀ p₄ p₅ + p₁ p₃ p₅ + p₂ p₃ p₄) H¹⁸
  - 302330880 (p₁ p₄² + p₂² p₅) H¹⁸ - 100776960 p₃³ H¹⁸
  + partitions-of-9 monomials + κ-block
  - (23514624 p₀ H¹⁵ + …) D - 3359232 p₁ H¹² E - (233280 p₂ H⁹ + …) F
  - (10368 p₃ H⁶ - …) G - (324 p₄ H³ - 81 p₅²) I - 36 p₅ J`,

kept in factored form through the third–eighth defects, via the exact
multiplier identity

`544195584 H²⁰ · row₆[p₆ = H³] = (2 H L' - 45 L H')
  + (23514624 p₀ H¹⁵ + …) rowD
  + 7838208 (p₁ H¹² + p₂ p₅ H⁹ + p₃ p₄ H⁹) rowE
  + (326592 p₂ H⁹ + …) rowF + (36288 p₃ H⁶ + …) rowG
  + (756 p₄ H³ + 189 p₅²) rowI + 252 p₅ rowJ`.

The row sees neither `q₉` nor `q₈` at all — the first aligned row with
an EMPTY source-correction module: there is no `N`-correction and no
`C`-correction of any kind.  On the aligned face every correction
vanishes, so `2 H L' = 45 L H'` and the weight-`45/2` first integral
`L² = κ₈ H⁴⁵` holds — ODD exponent, chambered like `D`, `F`, `I`.

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `E = κ₃ H¹⁰`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`,
  `I = ν₂ h₀³⁵`, `J = κ₇ H²⁰`): `L = μ₃ h₀⁴⁵` with `μ₃² = κ₈`.
  Cancelling `h₀³⁶` leaves the core `= μ₃ h₀⁹` whose `h₀`-free nonic
  head is
  `-5120 (α³ - 36 α² β z + 9 α² z³ - 36 α β³ + 270 α β² z² - 54 α β z⁴
  + 189 β⁴ z - 540 β³ z³ + 81 β² z⁵)`
  in `α = 27 p₃ - w₁³`, `β = 3 f₂ - w₁²`, `z = w₁` — every term of
  total `(α,β)`-degree at least two, with degree-two part
  `9 z³ (α - 3 β z)²`.  Substituting `e₁, e₂` and reducing along the
  eighth-face product divisor `u₂` peels `h₀³` to the peeled row
  `= μ₃ h₀⁶` with head `27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³` and
  `q₁` tied at `h₀⁵`.  At the root the head, the `u₂` root product,
  and the eighth-face combined-row cubic RESOLVE the eighth-face
  residual branch: `e₂(a) = 0` holds UNCONDITIONALLY, refined by
  `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)` — so the seventh-face divisor
  DEEPENS to `27 p₃ - w₁³ = h₀² e₃`, the first `h₀²`-deep
  divisibility of the aligned tower.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `I = 0`, `E = κ₃ H¹⁰`,
  `G = κ₅ H¹⁵`, `J = κ₇ H²⁰`): the odd exponent forces `κ₈ = 0` and
  `L ≡ 0`.  Cancelling `H¹⁸` and substituting `t₁, t₂` peels `H²`
  with head `-46080 g₁ (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the CARRIED
  eighth-face `p₂` divisor squared — so substituting `u` peels one
  more `H`, leaving the cubic head `-5120 (t₂ - 6 g₁ t₁)³`, which
  vanishes at BOTH simple roots and transfers to the NEW divisibility
  `t₂ - 6 g₁ t₁ = H t₃` with root pin `t₂(a) = 6 g₁(a) t₁(a)` (hence
  `27 p₂(a) = g₁(a)² t₁(a)`, refining the carried eighth-face `p₂`
  pin).  Substituting `t₃` peels the last `H` and `q₁` is solved
  OUTRIGHT: `1632586752 q₁ = … - 5120 H² t₃³`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`dvd_of_sq_dvd_sq_poly`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `e₃ = 0`, `u₂ = 0`,
`g₁ = 0`, `f = 0`, `t₁ = 0`, `t₂ = 0`, `t₃ = 0`, `u = 0`, `κ = 0`,
`μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`, `κ₇ = 0`,
`κ₈ = 0`, `μ₃ = 0`) are not excluded, and the constants `κ`,
`κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²`, `κ₇`, `κ₈ = μ₃²` are
preserved where not forced.  The square residual branch keeps both
alternatives; no individual vanishing of `p₀, p₁, p₂, p₃, q₁, q₂, q₃`
is claimed.  The next unused Keller row on the aligned face is the
degree-`5` Jacobian coefficient, the first row that sees `q₀` (pairs
`(0,6), (1,5), (2,4), (3,3), (4,2), (5,1), (6,0)`; expected
weight-`25` defect, even exponent, chamber-free like `E`, `G`, `J`).
No total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`6` Keller coefficient on the aligned face -/

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`6` Jacobian coefficient, the first
aligned row that sees `q₁`. -/
theorem alignedNinthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * q.coeff 1 +
        (p.coeff 5).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 1).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 2).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  rw [hC2, hC3, hC4, hC5, hC6, hC7]
  linear_combination hcoeff

/-! ## Aligned ninth defect -/
/-- Cleared ninth defect of the degree-`6` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, the seventh defect `I`,
and the eighth defect `J`.  On the aligned face it is a polynomial
first integral of weight `45/2`. -/
def alignedNinthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (1813985280 : K[X]) * a0 * a3 * H ^ 21 + (1813985280 : K[X]) * a1 * a2 * H
    ^ 21 - (1632586752 : K[X]) * b1 * H ^ 22 - (604661760 : K[X]) * a0 * a4
    * a5 * H ^ 18 - (604661760 : K[X]) * a1 * a3 * a5 * H ^ 18 - (302330880
    : K[X]) * a1 * a4 ^ 2 * H ^ 18 - (302330880 : K[X]) * a2 ^ 2 * a5 * H ^
    18 - (604661760 : K[X]) * a2 * a3 * a4 * H ^ 18 - (100776960 : K[X]) *
    a3 ^ 3 * H ^ 18 + (134369280 : K[X]) * a0 * a5 ^ 3 * H ^ 15 + (403107840
    : K[X]) * a1 * a4 * a5 ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a3 * a5
    ^ 2 * H ^ 15 + (403107840 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 15 +
    (403107840 : K[X]) * a3 ^ 2 * a4 * a5 * H ^ 15 + (134369280 : K[X]) * a3
    * a4 ^ 3 * H ^ 15 - (78382080 : K[X]) * a1 * a5 ^ 4 * H ^ 12 -
    (313528320 : K[X]) * a2 * a4 * a5 ^ 3 * H ^ 12 - (156764160 : K[X]) * a3
    ^ 2 * a5 ^ 3 * H ^ 12 - (470292480 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^
    12 - (78382080 : K[X]) * a4 ^ 4 * a5 * H ^ 12 + (52254720 : K[X]) * a2 *
    a5 ^ 5 * H ^ 9 + (261273600 : K[X]) * a3 * a4 * a5 ^ 4 * H ^ 9 +
    (174182400 : K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 9 - (37739520 : K[X]) * a3 *
    a5 ^ 6 * H ^ 6 - (113218560 : K[X]) * a4 ^ 2 * a5 ^ 5 * H ^ 6 +
    (28753920 : K[X]) * a4 * a5 ^ 7 * H ^ 3 - (2529280 : K[X]) * a5 ^ 9 +
    Polynomial.C κ * ((80621568 : K[X]) * a0 * a5 * H ^ 20 + (80621568 :
    K[X]) * a1 * a4 * H ^ 20 + (80621568 : K[X]) * a2 * a3 * H ^ 20 -
    (26873856 : K[X]) * a1 * a5 ^ 2 * H ^ 17 - (53747712 : K[X]) * a2 * a4 *
    a5 * H ^ 17 - (26873856 : K[X]) * a3 ^ 2 * a5 * H ^ 17 - (26873856 :
    K[X]) * a3 * a4 ^ 2 * H ^ 17 + (14929920 : K[X]) * a2 * a5 ^ 3 * H ^ 14
    + (44789760 : K[X]) * a3 * a4 * a5 ^ 2 * H ^ 14 + (14929920 : K[X]) * a4
    ^ 3 * a5 * H ^ 14 - (9953280 : K[X]) * a3 * a5 ^ 4 * H ^ 11 - (19906560
    : K[X]) * a4 ^ 2 * a5 ^ 3 * H ^ 11 + (7299072 : K[X]) * a4 * a5 ^ 5 * H
    ^ 8 - (811008 : K[X]) * a5 ^ 7 * H ^ 5) - ((23514624 : K[X]) * a0 * H ^
    15 + (3919104 : K[X]) * a1 * a5 * H ^ 12 + (3919104 : K[X]) * a2 * a4 *
    H ^ 12 + (1959552 : K[X]) * a3 ^ 2 * H ^ 12 - (1632960 : K[X]) * a2 * a5
    ^ 2 * H ^ 9 - (3265920 : K[X]) * a3 * a4 * a5 * H ^ 9 - (544320 : K[X])
    * a4 ^ 3 * H ^ 9 + (997920 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (1496880 :
    K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 - (706860 : K[X]) * a4 * a5 ^ 4 * H ^ 3
    + (90321 : K[X]) * a5 ^ 6) * alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (3359232 : K[X]) * a1 * H ^ 12 * alignedFourthDefect610 H a2 a3 a4 a5 b6
    b7 κ - ((233280 : K[X]) * a2 * H ^ 9 - (38880 : K[X]) * a3 * a5 * H ^ 6
    - (19440 : K[X]) * a4 ^ 2 * H ^ 6 + (22680 : K[X]) * a4 * a5 ^ 2 * H ^ 3
    - (4095 : K[X]) * a5 ^ 4) * alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6
    b7 κ - ((10368 : K[X]) * a3 * H ^ 6 - (3456 : K[X]) * a4 * a5 * H ^ 3 +
    (768 : K[X]) * a5 ^ 3) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5
    b6 b7 κ - ((324 : K[X]) * a4 * H ^ 3 - (81 : K[X]) * a5 ^ 2) *
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - (36 :
    K[X]) * a5 * alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6
    b7 κ

set_option maxHeartbeats 8000000000 in
/-- Exact combination of the degree-`6` Jacobian expression with the
weighted derivative of `L`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`7` rows.  The row sees neither `q₉` nor `q₈`, so there is no
`N`-correction and no `C`-correction — the source-correction module is
EMPTY. -/
theorem alignedNinthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (544195584 : K[X]) * H ^ 20 * ((H ^ 3).derivative * b1 + a5.derivative *
      (b2 * (2 : K[X])) + a4.derivative * (b3 * (3 : K[X])) + a3.derivative
      * (b4 * (4 : K[X])) + a2.derivative * (b5 * (5 : K[X])) +
      a1.derivative * (b6 * (6 : K[X])) + a0.derivative * (b7 * (7 : K[X]))
      - ((H ^ 3 * (6 : K[X])) * b1.derivative + (a5 * (5 : K[X])) *
      b2.derivative + (a4 * (4 : K[X])) * b3.derivative + (a3 * (3 : K[X]))
      * b4.derivative + (a2 * (2 : K[X])) * b5.derivative + a1 *
      b6.derivative)) = ((2 : K[X]) * H * (alignedNinthDefect610 H a0 a1 a2
      a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (45 : K[X]) *
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ *
      H.derivative) + ((23514624 : K[X]) * a0 * H ^ 15 + (27433728 : K[X]) *
      a1 * a5 * H ^ 12 + (27433728 : K[X]) * a2 * a4 * H ^ 12 + (13716864 :
      K[X]) * a3 ^ 2 * H ^ 12 + (2286144 : K[X]) * a2 * a5 ^ 2 * H ^ 9 +
      (4572288 : K[X]) * a3 * a4 * a5 * H ^ 9 + (762048 : K[X]) * a4 ^ 3 * H
      ^ 9 - (635040 : K[X]) * a3 * a5 ^ 3 * H ^ 6 - (952560 : K[X]) * a4 ^ 2
      * a5 ^ 2 * H ^ 6 + (291060 : K[X]) * a4 * a5 ^ 4 * H ^ 3 - (27489 :
      K[X]) * a5 ^ 6) * ((2 : K[X]) * H * (alignedThirdDefect610 H a3 a4 a5
      b7 κ).derivative - (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ
      * H.derivative) + ((7838208 : K[X]) * a1 * H ^ 12 + (7838208 : K[X]) *
      a2 * a5 * H ^ 9 + (7838208 : K[X]) * a3 * a4 * H ^ 9) * (H *
      (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative - (10 :
      K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ * H.derivative) +
      ((326592 : K[X]) * a2 * H ^ 9 + (272160 : K[X]) * a3 * a5 * H ^ 6 +
      (136080 : K[X]) * a4 ^ 2 * H ^ 6 - (22680 : K[X]) * a4 * a5 ^ 2 * H ^
      3 + (2205 : K[X]) * a5 ^ 4) * ((2 : K[X]) * H * (alignedFifthDefect610
      H a1 a2 a3 a4 a5 b5 b6 b7 κ).derivative - (25 : K[X]) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ * H.derivative) +
      ((36288 : K[X]) * a3 * H ^ 6 + (24192 : K[X]) * a4 * a5 * H ^ 3 -
      (1344 : K[X]) * a5 ^ 3) * (H * (alignedSixthDefect610 H a0 a1 a2 a3 a4
      a5 b4 b5 b6 b7 κ).derivative - (15 : K[X]) * alignedSixthDefect610 H
      a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ * H.derivative) + ((756 : K[X]) * a4 *
      H ^ 3 + (189 : K[X]) * a5 ^ 2) * ((2 : K[X]) * H *
      (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
      κ).derivative - (35 : K[X]) * alignedSeventhDefect610 H a0 a1 a2 a3 a4
      a5 b3 b4 b5 b6 b7 κ * H.derivative) + (252 : K[X]) * a5 * (H *
      (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
      κ).derivative - (20 : K[X]) * alignedEighthDefect610 H a0 a1 a2 a3 a4
      a5 b2 b3 b4 b5 b6 b7 κ * H.derivative) := by
  simp only [alignedNinthDefect610, alignedEighthDefect610,
    alignedSeventhDefect610, alignedSixthDefect610, alignedFifthDefect610,
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

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`7` rows, the degree-`6` row is the weighted derivative
`2 H L' - 45 L H' = 0`. -/
theorem alignedNinthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H * (alignedNinthDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
      κ).derivative - (45 : K[X]) * alignedNinthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedNinthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7] at hrow
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hJrow :=
    alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedNinthDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
    (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hDrow, hErow, hFrow, hGrow, hIrow, hJrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-`45/2` polynomial first integral of the aligned
`(6,10)` ninth defect: `L² = κ₈ H⁴⁵`.  The odd exponent forces a
square/nonsquare chamber split exactly as for `D`, `F`, and `I`. -/
theorem alignedNinthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₈ : K,
      alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff
        3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff 3)
        (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 = Polynomial.C
        κ₈ * H ^ 45 := by
  let L : K[X] :=
    alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff
      4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (45 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC45 : Polynomial.C (45 : K) = (45 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 45) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (45 : K) * H ^ (45 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 45 =
          L * H ^ 44 *
            (Polynomial.C (45 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC45, hC2]
        have hfac :
            (45 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 45 hH) hW

/-! ## Square chamber -/

/-- In the square chamber the squared weight-`45/2` integral has a
polynomial square root: `L = μ₃ h₀⁴⁵` with `μ₃² = κ₈`.  The constant
`μ₃` is preserved, not cleared. -/
theorem alignedSquareNinth_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₈ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 :
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₈ * H ^ 45) :
    ∃ μ₃ : K, μ₃ ^ 2 = κ₈ ∧
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ =
        Polynomial.C μ₃ * h0 ^ 45 := by
  set L : K[X] :=
    alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 45) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ := by
    have h90 := hL2
    rw [hG, hHsq] at h90
    apply mul_left_cancel₀ (pow_ne_zero 90 hh0)
    linear_combination h90
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₈
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₃, hμ⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨μ₃, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₃ ^ 2) = Polynomial.C κ₈ := by
      rw [Polynomial.C_pow, hμ, hG2]
    exact Polynomial.C_injective hCμ
  · rw [hG, ← hμ]
    ring

/-- Scalar resolution of the ninth-row peeled head against the
eighth-face root product and combined-row cubic: `x (v - 3 u x) = 0`,
`1280 u (3 u x - v)(6 u x - v) + 189 m x⁵ = 0`, and
`276480 u³ x³ - 5120 v³ - 189 m x⁶ = 0` force `v = 0` UNCONDITIONALLY,
refined by `x = 0 ∨ (m = 0 ∧ u = 0)`. -/
theorem alignedNinthSquareResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : 1280 * u * (3 * u * x - v) * (6 * u * x - v) +
      189 * m * x ^ 5 = 0)
    (h9 : 276480 * u ^ 3 * x ^ 3 - 5120 * v ^ 3 - 189 * m * x ^ 6 = 0) :
    v = 0 ∧ (x = 0 ∨ (m = 0 ∧ u = 0)) := by
  rcases mul_eq_zero.mp h1 with hx | hv
  · have h3 : (5120 : K) * v ^ 3 = 0 := by
      rw [hx] at h9
      linear_combination -h9
    have h4 : v ^ 3 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num : (5120 : K) ≠ 0)
    exact ⟨(pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h4,
      Or.inl hx⟩
  · have h5 : (189 : K) * (m * x ^ 5) = 0 := by
      linear_combination h2 + (1280 * u * (6 * u * x - v)) * hv
    have h6 : m * x ^ 5 = 0 :=
      (mul_eq_zero.mp h5).resolve_left (by norm_num : (189 : K) ≠ 0)
    rcases mul_eq_zero.mp h6 with hm | hx5
    · have h7 : (138240 : K) * (u * x) ^ 3 = 0 := by
        linear_combination h9 +
          (5120 * (v ^ 2 + 3 * u * x * v + 9 * u ^ 2 * x ^ 2)) * hv +
          (189 * x ^ 6) * hm
      have h8 : (u * x) ^ 3 = 0 :=
        (mul_eq_zero.mp h7).resolve_left
          (by norm_num : (138240 : K) ≠ 0)
      rcases mul_eq_zero.mp
          ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h8) with
        hu0 | hx0
      · have hv0 : v = 0 := by linear_combination hv + 3 * x * hu0
        exact ⟨hv0, Or.inr ⟨hm, hu0⟩⟩
      · have hv0 : v = 0 := by linear_combination hv + 3 * u * hx0
        exact ⟨hv0, Or.inl hx0⟩
    · have hx0 : x = 0 :=
        (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hx5
      have hv0 : v = 0 := by linear_combination hv + 3 * u * hx0
      exact ⟨hv0, Or.inl hx0⟩

/-- Thrice-peeled square-chamber form of the consumed degree-`6` row
(`h₀³⁶ · h₀³` cancelled along the seventh-face divisibilities and the
eighth-face product divisor `u₂`): head
`27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³`, `q₁` tied at `h₀⁵`.  On the
face it equals `μ₃ h₀⁶`. -/
def alignedNinthSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 a0 a1 a2 b1 : K[X]) (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) :
    K[X] :=
  ((276480 : K[X]) * e1 ^ 3 * w1 ^ 3 - (5120 : K[X]) * e2 ^ 3 - Polynomial.C
    μ * ((189 : K[X]) * w1 ^ 6)) + h0 * (-((967680 : K[X]) * e1 ^ 4 * w1) +
    (184320 : K[X]) * e1 ^ 3 * e2 - (829440 : K[X]) * e1 ^ 2 * u2 * w1 +
    (44789760 : K[X]) * e1 ^ 2 * w1 * a2 + (184320 : K[X]) * e1 * e2 * u2 -
    (7464960 : K[X]) * e1 * e2 * a2 - (46080 : K[X]) * u2 ^ 2 * w1 +
    (7464960 : K[X]) * u2 * w1 * a2 - (302330880 : K[X]) * w1 * a2 ^ 2 -
    Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^ 4)) + h0 ^ 2 * (Polynomial.C
    ν * ((135 : K[X]) * w1 ^ 4) + Polynomial.C μ * ((15120 : K[X]) * e1 ^ 2
    * w1 ^ 2) - Polynomial.C μ * ((2688 : K[X]) * e2 ^ 2) - Polynomial.C μ *
    ((2016 : K[X]) * u2 * w1 ^ 2) + Polynomial.C μ * ((326592 : K[X]) * w1 ^
    2 * a2) + Polynomial.C κ * ((552960 : K[X]) * e1 ^ 3 * w1) -
    Polynomial.C κ * ((110592 : K[X]) * e1 ^ 2 * e2) + Polynomial.C κ *
    ((221184 : K[X]) * e1 * u2 * w1) - Polynomial.C κ * ((17915904 : K[X]) *
    e1 * w1 * a2) - Polynomial.C κ * ((36864 : K[X]) * e2 * u2) +
    Polynomial.C κ * ((2985984 : K[X]) * e2 * a2)) + h0 ^ 3 * (-((33592320 :
    K[X]) * e1 ^ 2 * a1) - (22394880 : K[X]) * u2 * a1 + (1813985280 : K[X])
    * a1 * a2 + Polynomial.C ν * ((1080 : K[X]) * e1 * w1 ^ 2) +
    Polynomial.C μ * ((20160 : K[X]) * e1 ^ 3) + Polynomial.C μ * ((40320 :
    K[X]) * e1 * u2) - Polynomial.C μ * ((1306368 : K[X]) * e1 * a2)) + h0 ^
    4 * (-((201553920 : K[X]) * e1 * w1 * a0) + (67184640 : K[X]) * e2 * a0
    - Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + Polynomial.C κ₅ * ((1152 :
    K[X]) * e1 * w1) - Polynomial.C κ₅ * ((384 : K[X]) * e2) + Polynomial.C
    ν * ((2160 : K[X]) * e1 ^ 2) + Polynomial.C ν * ((1440 : K[X]) * u2) -
    Polynomial.C ν * ((233280 : K[X]) * a2) - Polynomial.C μ * ((3919104 :
    K[X]) * w1 * a1) + Polynomial.C κ * ((26873856 : K[X]) * e1 * a1)) + h0
    ^ 5 * (-((1632586752 : K[X]) * b1) - Polynomial.C κ₇ * ((36 : K[X]) *
    w1) - Polynomial.C ν₂ * ((108 : K[X]) * e1) - Polynomial.C κ₃ *
    ((3359232 : K[X]) * a1) + Polynomial.C κ * ((80621568 : K[X]) * w1 *
    a0)) + h0 ^ 6 * (-(Polynomial.C μ * ((23514624 : K[X]) * a0)))

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`6` row in the square chamber: the
`h₀³⁶`-peeled core absorbs the nonic head through the seventh-face
divisibilities and the eighth-face product divisor `u₂`, cancelling
`h₀³` into the peeled row `= μ₃ h₀⁶` with head
`27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³` and `q₁` tied at `h₀⁵`; at
the root of `h₀` the head, the `u₂` root product, and the eighth-face
combined-row cubic force `e₂(a) = 0`, and the linear-root transfer
DEEPENS the seventh-face divisor to `27 p₃ - w₁³ = h₀² e₃`. -/
theorem alignedSquareNinth_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 u2 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1) (hHsq : H = h0 ^ 2)
    (hp5 : a5 = h0 ^ 4 * w1) (hp4 : a4 = h0 ^ 2 * f2)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI : alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
      Polynomial.C ν₂ * h0 ^ 35)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = Polynomial.C μ₃ * h0 ^ 45)
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hu2 : w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2)
    (hQ9 : alignedEighthSquareCombinedRow610 h0 w1 e1 e2 a0 a1 a2 b2 b3
        κ μ κ₃ ν κ₅ ν₂ =
      Polynomial.C κ₇ * h0 ^ 5 +
        Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4)) :
    ∃ e3 : K[X],
      e2 = h0 * e3 ∧
      (27 : K[X]) * a3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
      alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 a0 a1 a2 b1
          κ μ κ₃ ν κ₅ ν₂ κ₇ = Polynomial.C μ₃ * h0 ^ 6 := by
  have hL' := hL
  simp only [alignedNinthDefect610] at hL'
  rw [hD, hE, hF, hG, hI, hJ, hHsq, hp5, hp4] at hL'
  have hcore :
      (-((78382080 : K[X]) * f2 ^ 4 * w1) + (134369280 : K[X]) * f2 ^ 3 * a3
        + (174182400 : K[X]) * f2 ^ 3 * w1 ^ 3 - (470292480 : K[X]) * f2 ^ 2
        * a3 * w1 ^ 2 - (113218560 : K[X]) * f2 ^ 2 * w1 ^ 5 + (403107840 :
        K[X]) * f2 * a3 ^ 2 * w1 + (261273600 : K[X]) * f2 * a3 * w1 ^ 4 +
        (28753920 : K[X]) * f2 * w1 ^ 7 - (100776960 : K[X]) * a3 ^ 3 -
        (156764160 : K[X]) * a3 ^ 2 * w1 ^ 3 - (37739520 : K[X]) * a3 * w1 ^
        6 - (2529280 : K[X]) * w1 ^ 9) + h0 ^ 2 * ((403107840 : K[X]) * f2 ^
        2 * w1 * a2 - (604661760 : K[X]) * f2 * a3 * a2 - (313528320 : K[X])
        * f2 * w1 ^ 3 * a2 + (403107840 : K[X]) * a3 * w1 ^ 2 * a2 +
        (52254720 : K[X]) * w1 ^ 5 * a2 + Polynomial.C κ * ((14929920 :
        K[X]) * f2 ^ 3 * w1) - Polynomial.C κ * ((26873856 : K[X]) * f2 ^ 2
        * a3) - Polynomial.C κ * ((19906560 : K[X]) * f2 ^ 2 * w1 ^ 3) +
        Polynomial.C κ * ((44789760 : K[X]) * f2 * a3 * w1 ^ 2) +
        Polynomial.C κ * ((7299072 : K[X]) * f2 * w1 ^ 5) - Polynomial.C κ *
        ((26873856 : K[X]) * a3 ^ 2 * w1) - Polynomial.C κ * ((9953280 :
        K[X]) * a3 * w1 ^ 4) - Polynomial.C κ * ((811008 : K[X]) * w1 ^ 7))
        + h0 ^ 3 * (Polynomial.C μ * ((544320 : K[X]) * f2 ^ 3) -
        Polynomial.C μ * ((1496880 : K[X]) * f2 ^ 2 * w1 ^ 2) + Polynomial.C
        μ * ((3265920 : K[X]) * f2 * a3 * w1) + Polynomial.C μ * ((706860 :
        K[X]) * f2 * w1 ^ 4) - Polynomial.C μ * ((1959552 : K[X]) * a3 ^ 2)
        - Polynomial.C μ * ((997920 : K[X]) * a3 * w1 ^ 3) - Polynomial.C μ
        * ((90321 : K[X]) * w1 ^ 6)) + h0 ^ 4 * (-((302330880 : K[X]) * f2 ^
        2 * a1) + (403107840 : K[X]) * f2 * w1 ^ 2 * a1 - (604661760 : K[X])
        * a3 * w1 * a1 - (78382080 : K[X]) * w1 ^ 4 * a1 - (302330880 :
        K[X]) * w1 * a2 ^ 2 - Polynomial.C κ * ((53747712 : K[X]) * f2 * w1
        * a2) + Polynomial.C κ * ((80621568 : K[X]) * a3 * a2) +
        Polynomial.C κ * ((14929920 : K[X]) * w1 ^ 3 * a2)) + h0 ^ 5 *
        (Polynomial.C ν * ((19440 : K[X]) * f2 ^ 2) - Polynomial.C ν *
        ((22680 : K[X]) * f2 * w1 ^ 2) + Polynomial.C ν * ((38880 : K[X]) *
        a3 * w1) + Polynomial.C ν * ((4095 : K[X]) * w1 ^ 4) - Polynomial.C
        μ * ((3919104 : K[X]) * f2 * a2) + Polynomial.C μ * ((1632960 :
        K[X]) * w1 ^ 2 * a2)) + h0 ^ 6 * (-((604661760 : K[X]) * f2 * w1 *
        a0) + (1813985280 : K[X]) * a3 * a0 + (134369280 : K[X]) * w1 ^ 3 *
        a0 + (1813985280 : K[X]) * a1 * a2 + Polynomial.C κ₅ * ((3456 :
        K[X]) * f2 * w1) - Polynomial.C κ₅ * ((10368 : K[X]) * a3) -
        Polynomial.C κ₅ * ((768 : K[X]) * w1 ^ 3) + Polynomial.C κ *
        ((80621568 : K[X]) * f2 * a1) - Polynomial.C κ * ((26873856 : K[X])
        * w1 ^ 2 * a1)) + h0 ^ 7 * (-(Polynomial.C ν₂ * ((324 : K[X]) * f2))
        + Polynomial.C ν₂ * ((81 : K[X]) * w1 ^ 2) - Polynomial.C ν *
        ((233280 : K[X]) * a2) - Polynomial.C μ * ((3919104 : K[X]) * w1 *
        a1)) + h0 ^ 8 * (-((1632586752 : K[X]) * b1) - Polynomial.C κ₇ *
        ((36 : K[X]) * w1) - Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0)) + h0 ^ 9 *
        (-(Polynomial.C μ * ((23514624 : K[X]) * a0))) = Polynomial.C μ₃ *
        h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 36 hh0)
    linear_combination hL'
  have hR9 :
      ((276480 : K[X]) * e1 ^ 3 * w1 ^ 3 - (5120 : K[X]) * e2 ^ 3 -
        Polynomial.C μ * ((189 : K[X]) * w1 ^ 6)) + h0 * (-((967680 : K[X])
        * e1 ^ 4 * w1) + (184320 : K[X]) * e1 ^ 3 * e2 - (829440 : K[X]) *
        e1 ^ 2 * u2 * w1 + (44789760 : K[X]) * e1 ^ 2 * w1 * a2 + (184320 :
        K[X]) * e1 * e2 * u2 - (7464960 : K[X]) * e1 * e2 * a2 - (46080 :
        K[X]) * u2 ^ 2 * w1 + (7464960 : K[X]) * u2 * w1 * a2 - (302330880 :
        K[X]) * w1 * a2 ^ 2 - Polynomial.C μ * ((2268 : K[X]) * e1 * w1 ^
        4)) + h0 ^ 2 * (Polynomial.C ν * ((135 : K[X]) * w1 ^ 4) +
        Polynomial.C μ * ((15120 : K[X]) * e1 ^ 2 * w1 ^ 2) - Polynomial.C μ
        * ((2688 : K[X]) * e2 ^ 2) - Polynomial.C μ * ((2016 : K[X]) * u2 *
        w1 ^ 2) + Polynomial.C μ * ((326592 : K[X]) * w1 ^ 2 * a2) +
        Polynomial.C κ * ((552960 : K[X]) * e1 ^ 3 * w1) - Polynomial.C κ *
        ((110592 : K[X]) * e1 ^ 2 * e2) + Polynomial.C κ * ((221184 : K[X])
        * e1 * u2 * w1) - Polynomial.C κ * ((17915904 : K[X]) * e1 * w1 *
        a2) - Polynomial.C κ * ((36864 : K[X]) * e2 * u2) + Polynomial.C κ *
        ((2985984 : K[X]) * e2 * a2)) + h0 ^ 3 * (-((33592320 : K[X]) * e1 ^
        2 * a1) - (22394880 : K[X]) * u2 * a1 + (1813985280 : K[X]) * a1 *
        a2 + Polynomial.C ν * ((1080 : K[X]) * e1 * w1 ^ 2) + Polynomial.C μ
        * ((20160 : K[X]) * e1 ^ 3) + Polynomial.C μ * ((40320 : K[X]) * e1
        * u2) - Polynomial.C μ * ((1306368 : K[X]) * e1 * a2)) + h0 ^ 4 *
        (-((201553920 : K[X]) * e1 * w1 * a0) + (67184640 : K[X]) * e2 * a0
        - Polynomial.C ν₂ * ((27 : K[X]) * w1 ^ 2) + Polynomial.C κ₅ *
        ((1152 : K[X]) * e1 * w1) - Polynomial.C κ₅ * ((384 : K[X]) * e2) +
        Polynomial.C ν * ((2160 : K[X]) * e1 ^ 2) + Polynomial.C ν * ((1440
        : K[X]) * u2) - Polynomial.C ν * ((233280 : K[X]) * a2) -
        Polynomial.C μ * ((3919104 : K[X]) * w1 * a1) + Polynomial.C κ *
        ((26873856 : K[X]) * e1 * a1)) + h0 ^ 5 * (-((1632586752 : K[X]) *
        b1) - Polynomial.C κ₇ * ((36 : K[X]) * w1) - Polynomial.C ν₂ * ((108
        : K[X]) * e1) - Polynomial.C κ₃ * ((3359232 : K[X]) * a1) +
        Polynomial.C κ * ((80621568 : K[X]) * w1 * a0)) + h0 ^ 6 *
        (-(Polynomial.C μ * ((23514624 : K[X]) * a0))) = Polynomial.C μ₃ *
        h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
    linear_combination hcore + (-(-((967680 : K[X]) * e1 ^ 3 * w1 * h0 ^ 3)
      + (3548160 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 ^ 2 - (2903040 : K[X]) * e1
      ^ 2 * w1 * f2 * h0 ^ 2 + (4976640 : K[X]) * e1 ^ 2 * a3 * h0 ^ 2 -
      (2580480 : K[X]) * e1 * w1 ^ 5 * h0 + (13547520 : K[X]) * e1 * w1 ^ 3
      * f2 * h0 - (42301440 : K[X]) * e1 * w1 ^ 2 * a3 * h0 - (8709120 :
      K[X]) * e1 * w1 * f2 ^ 2 * h0 + (44789760 : K[X]) * e1 * w1 * a2 * h0
      ^ 3 + (14929920 : K[X]) * e1 * f2 * a3 * h0 - (33592320 : K[X]) * e1 *
      a1 * h0 ^ 5 + (2488320 : K[X]) * w1 ^ 7 - (21288960 : K[X]) * w1 ^ 5 *
      f2 + (39813120 : K[X]) * w1 ^ 4 * a3 + (49351680 : K[X]) * w1 ^ 3 * f2
      ^ 2 - (59719680 : K[X]) * w1 ^ 3 * a2 * h0 ^ 2 - (141834240 : K[X]) *
      w1 ^ 2 * f2 * a3 + (100776960 : K[X]) * w1 ^ 2 * a1 * h0 ^ 4 -
      (26127360 : K[X]) * w1 * f2 ^ 3 + (134369280 : K[X]) * w1 * f2 * a2 *
      h0 ^ 2 + (134369280 : K[X]) * w1 * a3 ^ 2 - (201553920 : K[X]) * w1 *
      a0 * h0 ^ 6 + (44789760 : K[X]) * f2 ^ 2 * a3 - (100776960 : K[X]) *
      f2 * a1 * h0 ^ 4 - (201553920 : K[X]) * a3 * a2 * h0 ^ 2 -
      Polynomial.C ν₂ * ((108 : K[X]) * h0 ^ 7) + Polynomial.C κ₅ * ((1152 :
      K[X]) * w1 * h0 ^ 6) + Polynomial.C ν * ((2160 : K[X]) * e1 * h0 ^ 6)
      - Polynomial.C ν * ((5400 : K[X]) * w1 ^ 2 * h0 ^ 5) + Polynomial.C ν
      * ((6480 : K[X]) * f2 * h0 ^ 5) + Polynomial.C μ * ((20160 : K[X]) *
      e1 ^ 2 * h0 ^ 5) - Polynomial.C μ * ((126000 : K[X]) * e1 * w1 ^ 2 *
      h0 ^ 4) + Polynomial.C μ * ((60480 : K[X]) * e1 * f2 * h0 ^ 4) +
      Polynomial.C μ * ((89460 : K[X]) * w1 ^ 4 * h0 ^ 3) - Polynomial.C μ *
      ((438480 : K[X]) * w1 ^ 2 * f2 * h0 ^ 3) + Polynomial.C μ * ((1088640
      : K[X]) * w1 * a3 * h0 ^ 3) + Polynomial.C μ * ((181440 : K[X]) * f2 ^
      2 * h0 ^ 3) - Polynomial.C μ * ((1306368 : K[X]) * a2 * h0 ^ 5) +
      Polynomial.C κ * ((552960 : K[X]) * e1 ^ 2 * w1 * h0 ^ 4) -
      Polynomial.C κ * ((1105920 : K[X]) * e1 * w1 ^ 3 * h0 ^ 3) +
      Polynomial.C κ * ((1658880 : K[X]) * e1 * w1 * f2 * h0 ^ 3) -
      Polynomial.C κ * ((2985984 : K[X]) * e1 * a3 * h0 ^ 3) + Polynomial.C
      κ * ((774144 : K[X]) * w1 ^ 5 * h0 ^ 2) - Polynomial.C κ * ((4976640 :
      K[X]) * w1 ^ 3 * f2 * h0 ^ 2) + Polynomial.C κ * ((11943936 : K[X]) *
      w1 ^ 2 * a3 * h0 ^ 2) + Polynomial.C κ * ((4976640 : K[X]) * w1 * f2 ^
      2 * h0 ^ 2) - Polynomial.C κ * ((17915904 : K[X]) * w1 * a2 * h0 ^ 4)
      - Polynomial.C κ * ((8957952 : K[X]) * f2 * a3 * h0 ^ 2) +
      Polynomial.C κ * ((26873856 : K[X]) * a1 * h0 ^ 6))) * he1 +
      (-((184320 : K[X]) * e1 ^ 3 * h0 ^ 3 - (1382400 : K[X]) * e1 ^ 2 * w1
      ^ 2 * h0 ^ 2 + (184320 : K[X]) * e1 * e2 * w1 * h0 ^ 2 + (92160 :
      K[X]) * e1 * w1 ^ 4 * h0 + (4976640 : K[X]) * e1 * w1 * a3 * h0 -
      (7464960 : K[X]) * e1 * a2 * h0 ^ 3 - (5120 : K[X]) * e2 ^ 2 * h0 ^ 2
      - (40960 : K[X]) * e2 * w1 ^ 3 * h0 - (138240 : K[X]) * e2 * a3 * h0 +
      (40960 : K[X]) * w1 ^ 6 - (967680 : K[X]) * w1 ^ 3 * a3 + (7464960 :
      K[X]) * w1 ^ 2 * a2 * h0 ^ 2 - (22394880 : K[X]) * w1 * a1 * h0 ^ 4 -
      (3732480 : K[X]) * a3 ^ 2 + (67184640 : K[X]) * a0 * h0 ^ 6 -
      Polynomial.C κ₅ * ((384 : K[X]) * h0 ^ 6) + Polynomial.C ν * ((1440 :
      K[X]) * w1 * h0 ^ 5) + Polynomial.C μ * ((40320 : K[X]) * e1 * w1 * h0
      ^ 4) - Polynomial.C μ * ((2688 : K[X]) * e2 * h0 ^ 4) + Polynomial.C μ
      * ((672 : K[X]) * w1 ^ 3 * h0 ^ 3) - Polynomial.C μ * ((72576 : K[X])
      * a3 * h0 ^ 3) - Polynomial.C κ * ((110592 : K[X]) * e1 ^ 2 * h0 ^ 4)
      + Polynomial.C κ * ((331776 : K[X]) * e1 * w1 ^ 2 * h0 ^ 3) -
      Polynomial.C κ * ((36864 : K[X]) * e2 * w1 * h0 ^ 3) + Polynomial.C κ
      * ((36864 : K[X]) * w1 ^ 4 * h0 ^ 2) - Polynomial.C κ * ((995328 :
      K[X]) * w1 * a3 * h0 ^ 2) + Polynomial.C κ * ((2985984 : K[X]) * a2 *
      h0 ^ 4))) * he2 + (-(-((829440 : K[X]) * e1 ^ 2 * w1 * h0 ^ 3) +
      (184320 : K[X]) * e1 * e2 * h0 ^ 3 + (138240 : K[X]) * e1 * w1 ^ 3 *
      h0 ^ 2 - (46080 : K[X]) * e2 * w1 ^ 2 * h0 ^ 2 - (46080 : K[X]) * u2 *
      w1 * h0 ^ 3 + (7464960 : K[X]) * w1 * a2 * h0 ^ 3 - (22394880 : K[X])
      * a1 * h0 ^ 5 + Polynomial.C ν * ((1440 : K[X]) * h0 ^ 6) +
      Polynomial.C μ * ((40320 : K[X]) * e1 * h0 ^ 5) - Polynomial.C μ *
      ((2016 : K[X]) * w1 ^ 2 * h0 ^ 4) + Polynomial.C κ * ((221184 : K[X])
      * e1 * w1 * h0 ^ 4) - Polynomial.C κ * ((36864 : K[X]) * e2 * h0 ^
      4))) * hu2
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev1 := congrArg (fun t : K[X] => t.eval (-(d / c))) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at hev1
  rw [hroot, zero_mul] at hev1
  have h1 : w1.eval (-(d / c)) *
      (e2.eval (-(d / c)) -
        3 * e1.eval (-(d / c)) * w1.eval (-(d / c))) = 0 := by
    linear_combination hev1
  have hevQ9 := congrArg (fun t : K[X] => t.eval (-(d / c))) hQ9
  simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevQ9
  rw [hroot] at hevQ9
  have h2 : 1280 * e1.eval (-(d / c)) *
      (3 * e1.eval (-(d / c)) * w1.eval (-(d / c)) -
        e2.eval (-(d / c))) *
      (6 * e1.eval (-(d / c)) * w1.eval (-(d / c)) -
        e2.eval (-(d / c))) +
      189 * μ * w1.eval (-(d / c)) ^ 5 = 0 := by
    linear_combination -hevQ9
  have hevR9 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR9
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_neg, Polynomial.eval_ofNat] at hevR9
  rw [hroot] at hevR9
  have h9 : 276480 * e1.eval (-(d / c)) ^ 3 * w1.eval (-(d / c)) ^ 3 -
      5120 * e2.eval (-(d / c)) ^ 3 -
      189 * μ * w1.eval (-(d / c)) ^ 6 = 0 := by
    linear_combination hevR9
  obtain ⟨hv0, _hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
  obtain ⟨e3, he3⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0 e2
    (-(d / c)) hdeg1 hroot hv0
  refine ⟨e3, he3, ?_, ?_⟩
  · rw [he2, he3]
    ring
  · simp only [alignedNinthSquarePeeledRow610]
    linear_combination hR9

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent forces both the constant
and the ninth defect itself to vanish: `κ₈ = 0` and `L ≡ 0`. -/
theorem alignedNonsquareNinth_defect_eq_zero_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : k[X]} {κ κ₈ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hL2 :
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₈ * H ^ 45) :
    κ₈ = 0 ∧
      alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : k[X] :=
    alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 22) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 44 hH)
    have h44 := hL2
    rw [hG] at h44
    linear_combination h44
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₈ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk8 : κ₈ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk8]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk8, hLzero⟩

/-- Solved block of the nonsquare ninth row after the carried
eighth-face `u`-substitution and the new `t₃`-substitution peel the
last two powers of `H`: `1632586752 q₁` equals this block outright. -/
def alignedNinthNonsquareSolved610 {K : Type*} [CommRing K]
    (H g1 t1 t2 u t3 a0 a1 : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (-((967680 : K[X]) * t1 ^ 4 * g1) + (184320 : K[X]) * t1 ^ 3 * t2 +
    (552960 : K[X]) * t1 ^ 2 * u * g1 - (33592320 : K[X]) * t1 ^ 2 * a1 -
    (92160 : K[X]) * t1 * t2 * u - (201553920 : K[X]) * t1 * g1 * a0 +
    (67184640 : K[X]) * t2 * a0 - (46080 : K[X]) * u ^ 2 * g1 + (22394880 :
    K[X]) * u * a1 - Polynomial.C κ₇ * ((36 : K[X]) * g1) + Polynomial.C κ₅
    * ((1152 : K[X]) * t1 * g1) - Polynomial.C κ₅ * ((384 : K[X]) * t2) -
    Polynomial.C κ₃ * ((3359232 : K[X]) * a1) + Polynomial.C κ * ((552960 :
    K[X]) * t1 ^ 3 * g1) - Polynomial.C κ * ((110592 : K[X]) * t1 ^ 2 * t2)
    - Polynomial.C κ * ((221184 : K[X]) * t1 * u * g1) + Polynomial.C κ *
    ((26873856 : K[X]) * t1 * a1) + Polynomial.C κ * ((36864 : K[X]) * t2 *
    u) + Polynomial.C κ * ((80621568 : K[X]) * g1 * a0)) + H ^ 2 * (-((5120
    : K[X]) * t3 ^ 3))

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`6` row in the nonsquare chamber:
the `H¹⁸`-peeled core (the ninth defect vanishes identically) absorbs
the nonic head through the seventh-face divisibilities, peeling `H²`
onto the head `-46080 g₁ (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the CARRIED
eighth-face `p₂` divisor squared — so substituting `u` peels one more
`H` onto the cubic head `-5120 (t₂ - 6 g₁ t₁)³`, which vanishes at
BOTH simple roots and transfers to the NEW divisibility
`t₂ - 6 g₁ t₁ = H t₃`; substituting `t₃` peels the last `H` and
solves `q₁` OUTRIGHT. -/
theorem alignedNonsquareNinth_descent_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 f t1 t2 u a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : k[X]}
    {κ κ₃ κ₅ κ₇ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hE : alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
      Polynomial.C κ₃ * H ^ 10)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL0 : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = 0)
    (ht1 : (3 : k[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : k[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u) :
    ∃ t3 : k[X],
      t2 - (6 : k[X]) * g1 * t1 = H * t3 ∧
      (1632586752 : k[X]) * b1 =
        alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
          κ κ₃ κ₅ κ₇ := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hL' := hL0
  simp only [alignedNinthDefect610] at hL'
  rw [hD0, hE, hF0, hG, hI0, hJ, hg1, hf] at hL'
  have hcore :
      (-((78382080 : k[X]) * f ^ 4 * g1) + (134369280 : k[X]) * f ^ 3 * a3 +
        (174182400 : k[X]) * f ^ 3 * g1 ^ 3 - (470292480 : k[X]) * f ^ 2 *
        a3 * g1 ^ 2 - (113218560 : k[X]) * f ^ 2 * g1 ^ 5 + (403107840 :
        k[X]) * f * a3 ^ 2 * g1 + (261273600 : k[X]) * f * a3 * g1 ^ 4 +
        (28753920 : k[X]) * f * g1 ^ 7 - (100776960 : k[X]) * a3 ^ 3 -
        (156764160 : k[X]) * a3 ^ 2 * g1 ^ 3 - (37739520 : k[X]) * a3 * g1 ^
        6 - (2529280 : k[X]) * g1 ^ 9) + H * ((403107840 : k[X]) * f ^ 2 *
        g1 * a2 - (604661760 : k[X]) * f * a3 * a2 - (313528320 : k[X]) * f
        * g1 ^ 3 * a2 + (403107840 : k[X]) * a3 * g1 ^ 2 * a2 + (52254720 :
        k[X]) * g1 ^ 5 * a2 + Polynomial.C κ * ((14929920 : k[X]) * f ^ 3 *
        g1) - Polynomial.C κ * ((26873856 : k[X]) * f ^ 2 * a3) -
        Polynomial.C κ * ((19906560 : k[X]) * f ^ 2 * g1 ^ 3) + Polynomial.C
        κ * ((44789760 : k[X]) * f * a3 * g1 ^ 2) + Polynomial.C κ *
        ((7299072 : k[X]) * f * g1 ^ 5) - Polynomial.C κ * ((26873856 :
        k[X]) * a3 ^ 2 * g1) - Polynomial.C κ * ((9953280 : k[X]) * a3 * g1
        ^ 4) - Polynomial.C κ * ((811008 : k[X]) * g1 ^ 7)) + H ^ 2 *
        (-((302330880 : k[X]) * f ^ 2 * a1) + (403107840 : k[X]) * f * g1 ^
        2 * a1 - (604661760 : k[X]) * a3 * g1 * a1 - (78382080 : k[X]) * g1
        ^ 4 * a1 - (302330880 : k[X]) * g1 * a2 ^ 2 - Polynomial.C κ *
        ((53747712 : k[X]) * f * g1 * a2) + Polynomial.C κ * ((80621568 :
        k[X]) * a3 * a2) + Polynomial.C κ * ((14929920 : k[X]) * g1 ^ 3 *
        a2)) + H ^ 3 * (-((604661760 : k[X]) * f * g1 * a0) + (1813985280 :
        k[X]) * a3 * a0 + (134369280 : k[X]) * g1 ^ 3 * a0 + (1813985280 :
        k[X]) * a1 * a2 + Polynomial.C κ₅ * ((3456 : k[X]) * f * g1) -
        Polynomial.C κ₅ * ((10368 : k[X]) * a3) - Polynomial.C κ₅ * ((768 :
        k[X]) * g1 ^ 3) + Polynomial.C κ * ((80621568 : k[X]) * f * a1) -
        Polynomial.C κ * ((26873856 : k[X]) * g1 ^ 2 * a1)) + H ^ 4 *
        (-((1632586752 : k[X]) * b1) - Polynomial.C κ₇ * ((36 : k[X]) * g1)
        - Polynomial.C κ₃ * ((3359232 : k[X]) * a1) + Polynomial.C κ *
        ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hH)
    linear_combination hL'
  have hR2 :
      (-((414720 : k[X]) * t1 ^ 2 * g1 ^ 5) + (276480 : k[X]) * t1 * t2 * g1
        ^ 4 - (22394880 : k[X]) * t1 * g1 ^ 3 * a2 - (46080 : k[X]) * t2 ^ 2
        * g1 ^ 3 + (7464960 : k[X]) * t2 * g1 ^ 2 * a2 - (302330880 : k[X])
        * g1 * a2 ^ 2) + H * ((2764800 : k[X]) * t1 ^ 3 * g1 ^ 3 - (1382400
        : k[X]) * t1 ^ 2 * t2 * g1 ^ 2 + (44789760 : k[X]) * t1 ^ 2 * g1 *
        a2 + (184320 : k[X]) * t1 * t2 ^ 2 * g1 - (7464960 : k[X]) * t1 * t2
        * a2 + (67184640 : k[X]) * t1 * g1 ^ 2 * a1 - (5120 : k[X]) * t2 ^ 3
        - (22394880 : k[X]) * t2 * g1 * a1 + (1813985280 : k[X]) * a1 * a2 -
        Polynomial.C κ * ((663552 : k[X]) * t1 ^ 2 * g1 ^ 3) + Polynomial.C
        κ * ((331776 : k[X]) * t1 * t2 * g1 ^ 2) - Polynomial.C κ *
        ((17915904 : k[X]) * t1 * g1 * a2) - Polynomial.C κ * ((36864 :
        k[X]) * t2 ^ 2 * g1) + Polynomial.C κ * ((2985984 : k[X]) * t2 *
        a2)) + H ^ 2 * (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) *
        t1 ^ 3 * t2 - (33592320 : k[X]) * t1 ^ 2 * a1 - (201553920 : k[X]) *
        t1 * g1 * a0 + (67184640 : k[X]) * t2 * a0 - (1632586752 : k[X]) *
        b1 - Polynomial.C κ₇ * ((36 : k[X]) * g1) + Polynomial.C κ₅ * ((1152
        : k[X]) * t1 * g1) - Polynomial.C κ₅ * ((384 : k[X]) * t2) -
        Polynomial.C κ₃ * ((3359232 : k[X]) * a1) + Polynomial.C κ *
        ((552960 : k[X]) * t1 ^ 3 * g1) - Polynomial.C κ * ((110592 : k[X])
        * t1 ^ 2 * t2) + Polynomial.C κ * ((26873856 : k[X]) * t1 * a1) +
        Polynomial.C κ * ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-(-((967680 : k[X]) * t1 ^ 3 * g1 * H ^ 3) +
      (3548160 : k[X]) * t1 ^ 2 * g1 ^ 3 * H ^ 2 - (2903040 : k[X]) * t1 ^ 2
      * g1 * f * H ^ 2 + (4976640 : k[X]) * t1 ^ 2 * a3 * H ^ 2 - (2580480 :
      k[X]) * t1 * g1 ^ 5 * H + (13547520 : k[X]) * t1 * g1 ^ 3 * f * H -
      (42301440 : k[X]) * t1 * g1 ^ 2 * a3 * H - (8709120 : k[X]) * t1 * g1
      * f ^ 2 * H + (44789760 : k[X]) * t1 * g1 * a2 * H ^ 2 + (14929920 :
      k[X]) * t1 * f * a3 * H - (33592320 : k[X]) * t1 * a1 * H ^ 3 +
      (2488320 : k[X]) * g1 ^ 7 - (21288960 : k[X]) * g1 ^ 5 * f + (39813120
      : k[X]) * g1 ^ 4 * a3 + (49351680 : k[X]) * g1 ^ 3 * f ^ 2 - (59719680
      : k[X]) * g1 ^ 3 * a2 * H - (141834240 : k[X]) * g1 ^ 2 * f * a3 +
      (100776960 : k[X]) * g1 ^ 2 * a1 * H ^ 2 - (26127360 : k[X]) * g1 * f
      ^ 3 + (134369280 : k[X]) * g1 * f * a2 * H + (134369280 : k[X]) * g1 *
      a3 ^ 2 - (201553920 : k[X]) * g1 * a0 * H ^ 3 + (44789760 : k[X]) * f
      ^ 2 * a3 - (100776960 : k[X]) * f * a1 * H ^ 2 - (201553920 : k[X]) *
      a3 * a2 * H + Polynomial.C κ₅ * ((1152 : k[X]) * g1 * H ^ 3) +
      Polynomial.C κ * ((552960 : k[X]) * t1 ^ 2 * g1 * H ^ 3) -
      Polynomial.C κ * ((1105920 : k[X]) * t1 * g1 ^ 3 * H ^ 2) +
      Polynomial.C κ * ((1658880 : k[X]) * t1 * g1 * f * H ^ 2) -
      Polynomial.C κ * ((2985984 : k[X]) * t1 * a3 * H ^ 2) + Polynomial.C κ
      * ((774144 : k[X]) * g1 ^ 5 * H) - Polynomial.C κ * ((4976640 : k[X])
      * g1 ^ 3 * f * H) + Polynomial.C κ * ((11943936 : k[X]) * g1 ^ 2 * a3
      * H) + Polynomial.C κ * ((4976640 : k[X]) * g1 * f ^ 2 * H) -
      Polynomial.C κ * ((17915904 : k[X]) * g1 * a2 * H ^ 2) - Polynomial.C
      κ * ((8957952 : k[X]) * f * a3 * H) + Polynomial.C κ * ((26873856 :
      k[X]) * a1 * H ^ 3))) * ht1 + (-((184320 : k[X]) * t1 ^ 3 * H ^ 3 -
      (1382400 : k[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 2 + (184320 : k[X]) * t1 * t2
      * g1 * H ^ 2 + (92160 : k[X]) * t1 * g1 ^ 4 * H + (4976640 : k[X]) *
      t1 * g1 * a3 * H - (7464960 : k[X]) * t1 * a2 * H ^ 2 - (5120 : k[X])
      * t2 ^ 2 * H ^ 2 - (40960 : k[X]) * t2 * g1 ^ 3 * H - (138240 : k[X])
      * t2 * a3 * H + (40960 : k[X]) * g1 ^ 6 - (967680 : k[X]) * g1 ^ 3 *
      a3 + (7464960 : k[X]) * g1 ^ 2 * a2 * H - (22394880 : k[X]) * g1 * a1
      * H ^ 2 - (3732480 : k[X]) * a3 ^ 2 + (67184640 : k[X]) * a0 * H ^ 3 -
      Polynomial.C κ₅ * ((384 : k[X]) * H ^ 3) - Polynomial.C κ * ((110592 :
      k[X]) * t1 ^ 2 * H ^ 3) + Polynomial.C κ * ((331776 : k[X]) * t1 * g1
      ^ 2 * H ^ 2) - Polynomial.C κ * ((36864 : k[X]) * t2 * g1 * H ^ 2) +
      Polynomial.C κ * ((36864 : k[X]) * g1 ^ 4 * H) - Polynomial.C κ *
      ((995328 : k[X]) * g1 * a3 * H) + Polynomial.C κ * ((2985984 : k[X]) *
      a2 * H ^ 2))) * ht2
  have hR3 :
      ((1105920 : k[X]) * t1 ^ 3 * g1 ^ 3 - (552960 : k[X]) * t1 ^ 2 * t2 *
        g1 ^ 2 + (92160 : k[X]) * t1 * t2 ^ 2 * g1 - (5120 : k[X]) * t2 ^ 3)
        + H * (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) * t1 ^ 3 *
        t2 + (552960 : k[X]) * t1 ^ 2 * u * g1 - (33592320 : k[X]) * t1 ^ 2
        * a1 - (92160 : k[X]) * t1 * t2 * u - (201553920 : k[X]) * t1 * g1 *
        a0 + (67184640 : k[X]) * t2 * a0 - (46080 : k[X]) * u ^ 2 * g1 +
        (22394880 : k[X]) * u * a1 - (1632586752 : k[X]) * b1 - Polynomial.C
        κ₇ * ((36 : k[X]) * g1) + Polynomial.C κ₅ * ((1152 : k[X]) * t1 *
        g1) - Polynomial.C κ₅ * ((384 : k[X]) * t2) - Polynomial.C κ₃ *
        ((3359232 : k[X]) * a1) + Polynomial.C κ * ((552960 : k[X]) * t1 ^ 3
        * g1) - Polynomial.C κ * ((110592 : k[X]) * t1 ^ 2 * t2) -
        Polynomial.C κ * ((221184 : k[X]) * t1 * u * g1) + Polynomial.C κ *
        ((26873856 : k[X]) * t1 * a1) + Polynomial.C κ * ((36864 : k[X]) *
        t2 * u) + Polynomial.C κ * ((80621568 : k[X]) * g1 * a0)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2 + (-((552960 : k[X]) * t1 ^ 2 * g1 * H - (92160 :
      k[X]) * t1 * t2 * H - (138240 : k[X]) * t1 * g1 ^ 3 + (46080 : k[X]) *
      t2 * g1 ^ 2 - (46080 : k[X]) * u * g1 * H - (3732480 : k[X]) * g1 * a2
      + (22394880 : k[X]) * a1 * H - Polynomial.C κ * ((221184 : k[X]) * t1
      * g1 * H) + Polynomial.C κ * ((36864 : k[X]) * t2 * H))) * hu
  have hkey : ∀ a : k, H.eval a = 0 →
      (t2 - (6 : k[X]) * g1 * t1).eval a = 0 := by
    intro a ha
    have hev := congrArg (fun t : k[X] => t.eval a) hR3
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat, Polynomial.eval_zero] at hev
    rw [ha] at hev
    have hcube : ((t2 - (6 : k[X]) * g1 * t1).eval a) ^ 3 = 0 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      linear_combination (-(5120 : k)⁻¹) * hev
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  obtain ⟨t3, ht3⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkey
  have hq1 :
      (1632586752 : k[X]) * b1 =
        (-((967680 : k[X]) * t1 ^ 4 * g1) + (184320 : k[X]) * t1 ^ 3 * t2 +
          (552960 : k[X]) * t1 ^ 2 * u * g1 - (33592320 : k[X]) * t1 ^ 2 *
          a1 - (92160 : k[X]) * t1 * t2 * u - (201553920 : k[X]) * t1 * g1 *
          a0 + (67184640 : k[X]) * t2 * a0 - (46080 : k[X]) * u ^ 2 * g1 +
          (22394880 : k[X]) * u * a1 - Polynomial.C κ₇ * ((36 : k[X]) * g1)
          + Polynomial.C κ₅ * ((1152 : k[X]) * t1 * g1) - Polynomial.C κ₅ *
          ((384 : k[X]) * t2) - Polynomial.C κ₃ * ((3359232 : k[X]) * a1) +
          Polynomial.C κ * ((552960 : k[X]) * t1 ^ 3 * g1) - Polynomial.C κ
          * ((110592 : k[X]) * t1 ^ 2 * t2) - Polynomial.C κ * ((221184 :
          k[X]) * t1 * u * g1) + Polynomial.C κ * ((26873856 : k[X]) * t1 *
          a1) + Polynomial.C κ * ((36864 : k[X]) * t2 * u) + Polynomial.C κ
          * ((80621568 : k[X]) * g1 * a0)) + H ^ 2 * (-((5120 : k[X]) * t3 ^
          3)) := by
    apply mul_left_cancel₀ hH
    linear_combination -hR3 + (-((184320 : k[X]) * t1 ^ 2 * g1 ^ 2) + (61440
      : k[X]) * t1 * t2 * g1 + (30720 : k[X]) * t1 * t3 * g1 * H - (5120 :
      k[X]) * t2 ^ 2 - (5120 : k[X]) * t2 * t3 * H - (5120 : k[X]) * t3 ^ 2
      * H ^ 2) * ht3
  refine ⟨t3, ht3, ?_⟩
  simp only [alignedNinthNonsquareSolved610]
  linear_combination hq1

/-! ## Source-facing ninth-row packets -/

/-- Source-facing squared weight-`45/2` integral of a normalized
aligned scale-two `(6,10)` source: the degree-`6` row is consumed into
`L² = κ₈ H⁴⁵` on top of the previous aligned packet.  The odd exponent
is chambered. -/
theorem normalized610ScaleTwo_alignedNinthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ : K),
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
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₆ * H ^ 35 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ ^ 2 =
          Polynomial.C κ₈ * H ^ 45 := by
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
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, aligned_q9_solved_610 haligned,
    hM, hD2, hE, hF2, hG, hI2, hJ, hL2⟩

/-- Exact square-chamber ninth packet of a normalized aligned
scale-two `(6,10)` source: `L = μ₃ h₀⁴⁵` with `μ₃² = κ₈` preserved,
the thrice-peeled row with head
`27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³` and `q₁` tied at `h₀⁵`, the
carried eighth-face rows, and the NEW deepened divisibility
`27 p₃ - w₁³ = h₀² e₃`. -/
theorem normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ ν κ₅ ν₂ κ₇ κ₈ μ₃ : K) (w1 f2 e1 e2 u2 e3 : K[X]),
      μ₃ ^ 2 = κ₈ ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = h0 ^ 4 * w1 ∧
        p.coeff 4 = h0 ^ 2 * f2 ∧
        (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
        w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
        alignedEighthSquarePeeledRow610 h0 w1 e1 e2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ =
          Polynomial.C κ₇ * h0 ^ 6 ∧
        e2 = h0 * e3 ∧
        (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
        alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ =
          Polynomial.C μ₃ * h0 ^ 6 ∧
        alignedEighthSquareCombinedRow610 h0 w1 e1 e2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) (q.coeff 3)
            κ μ κ₃ ν κ₅ ν₂ =
          Polynomial.C κ₇ * h0 ^ 5 +
            Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) ∧
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
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₂ * h0 ^ 35 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ =
          Polynomial.C μ₃ * h0 ^ 45 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
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
  have hpacket8 :=
    normalized610ScaleTwo_alignedEighthFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket8
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, w1, f2, e1, e2, u2, hM, hp5w1, hp4f2,
    he1, he2, hu2, hR8, hQ9, hD, hE, hF, hG, hI, hJ⟩ := hpacket8
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨μ₃, hμ₃, hL⟩ := alignedSquareNinth_sqrt_610 hh0 hHsq hL2
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨e3, he3, h27, hR9⟩ :=
    alignedSquareNinth_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hE hF
      hG hI hJ hL he1 he2 hu2 hQ9
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, w1, f2, e1, e2, u2, e3, hμ₃,
    hM, hp5w1, hp4f2, he1, he2, hu2, hR8, he3, h27, hR9, hQ9, hD, hE,
    hF, hG, hI, hJ, hL⟩

/-- Exact nonsquare-chamber ninth packet of a normalized aligned
scale-two `(6,10)` source: the odd exponent forces `κ₈ = 0` and
`L ≡ 0`, the carried eighth-face divisor `81 p₂ + 3 g₁² t₁ - g₁ t₂ =
H u` peels the perfect-square head, the NEW divisibility
`t₂ - 6 g₁ t₁ = H t₃` transfers the cubic head, and `q₁` is solved
OUTRIGHT on top of the carried solved `q₂`. -/
theorem normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ : K) (g1 f t1 t2 u t3 : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (1632586752 : K[X]) * q.coeff 1 =
          alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 (p.coeff 0)
            (p.coeff 1) κ κ₃ κ₅ κ₇ ∧
        (15116544 : K[X]) * q.coeff 2 =
          alignedEighthNonsquareSolved610 H g1 t1 t2 u (p.coeff 0)
              (p.coeff 1) κ κ₃ κ₅ -
            Polynomial.C κ₇ * H ∧
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
          Polynomial.C κ₅ * H ^ 15 ∧
        alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4)
            (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 20 ∧
        alignedNinthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2)
            (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
            κ = 0 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
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
  have hpacket8 :=
    normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket8
  obtain ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, hM, hp5, hf, ht1, ht2, hu,
    _hR8, hq2, hD0, hE, hF0, hG, hI0, hJ⟩ := hpacket8
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk8, hL0⟩ :=
    alignedNonsquareNinth_defect_eq_zero_610 hH hHdegree hnsq hL2
  obtain ⟨t3, ht3, hq1⟩ :=
    alignedNonsquareNinth_descent_610 hH hHdegree hnsq hp5 hf hD0 hE
      hF0 hG hI0 hJ hL0 ht1 ht2 hu
  exact ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, t3, hM, hp5, hf, ht1, ht2,
    hu, ht3, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`6`
aligned row (peeled rows, solved `q₁`, and factored defect relations
are in the two chamber packets above).  Neither chamber is excluded
and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedNinthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (w1 f2 e1 e2 u2 e3 : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t1 t2 u t3 : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, w1, f2, e1, e2, u2, e3,
      _hμ₃, _hM, hp5, hp4, he1, he2, hu2, _hR8, _he3, h27, _hR9, _hQ9,
      _hD, _hE, _hF, _hG, _hI, _hJ, _hL⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, w1, f2, e1, e2, u2, e3, hp5, hp4,
      he1, he2, hu2, h27⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, t3, _hM, hp5, hf, ht1,
      ht2, hu, ht3, _hq1, _hq2, _hD0, _hE, _hF0, _hG, _hI0, _hJ,
      _hL0⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t1, t2, u, t3, hp5, hf, ht1, ht2, hu,
      ht3⟩

/-- Root data of the consumed degree-`6` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇, p₄, q₆` vanishes and
the seventh-face pins hold; in the square chamber the ninth-row head,
the eighth-face `u₂` root product, and the eighth-face combined-row
cubic RESOLVE the residual branch to `e₂(a) = 0` UNCONDITIONALLY,
refined by `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)`, and in the nonsquare
chamber the cubic head pins `t₂(a) = 6 g₁(a) t₁(a)`, refining the
carried `p₂` pin to `27 p₂(a) = g₁(a)² t₁(a)`. -/
theorem normalized610ScaleTwo_alignedNinthFace_rootData
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
      ((∃ h0 w1 f2 e1 e2 e3 : K[X], ∃ κ μ : K, h0 ≠ 0 ∧ H = h0 ^ 2 ∧
          h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          e2 = h0 * e3 ∧
          alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
            Polynomial.C κ * H ^ 5 ∧
          alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
          3 * f2.eval a = w1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = w1.eval a ^ 3 ∧
          e2.eval a = 0 ∧
          (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0))) ∨
        (∃ g1 f t1 t2 u t3 : K[X], p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
          3 * f.eval a = g1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = g1.eval a ^ 3 ∧
          81 * (p.coeff 2).eval a =
            g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a ∧
          t2.eval a = 6 * g1.eval a * t1.eval a ∧
          27 * (p.coeff 2).eval a = g1.eval a ^ 2 * t1.eval a)) := by
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
    have hpacket9 :=
      normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket9
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, ν₂B, κ₇B, κ₈B, μ₃B, w1, f2, e1, e2,
      u2, e3, _hμ₃, hM9, hp5w1, hp4f2, he1, he2, hu2, _hR8, he3, _h27,
      hR9, hQ9, hD9, _hE, _hF, _hG, _hI, _hJ, _hL⟩ := hpacket9
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
    have hpin1 : 3 * f2.eval a = w1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = w1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hev1 := congrArg (fun t : K[X] => t.eval a) hu2
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_ofNat] at hev1
    rw [hroot, zero_mul] at hev1
    have h1 : w1.eval a *
        (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 := by
      linear_combination hev1
    have hevQ9 := congrArg (fun t : K[X] => t.eval a) hQ9
    simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevQ9
    rw [hroot] at hevQ9
    have h2 : 1280 * e1.eval a *
        (3 * e1.eval a * w1.eval a - e2.eval a) *
        (6 * e1.eval a * w1.eval a - e2.eval a) +
        189 * μB * w1.eval a ^ 5 = 0 := by
      linear_combination -hevQ9
    have hevR9 := congrArg (fun t : K[X] => t.eval a) hR9
    simp only [alignedNinthSquarePeeledRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevR9
    rw [hroot] at hevR9
    have h9 : 276480 * e1.eval a ^ 3 * w1.eval a ^ 3 -
        5120 * e2.eval a ^ 3 - 189 * μB * w1.eval a ^ 6 = 0 := by
      linear_combination hevR9
    obtain ⟨hv0, hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, e1, e2, e3, κB, μB, hh0, hHsq, hroot, hp5w1,
        hp4f2, he1, he2, he3, hM9, hD9, hpin1, hpin2, hv0, hbranch⟩⟩
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
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, κ₃A, g1', f', _hp5', hq9, hq8, hq7, _hf', hq6, _hq5',
      _hD0', _hE', _hF0'⟩ := hpacket5
    have hpacket9 :=
      normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket9
    obtain ⟨κB, κ₃B, κ₅B, κ₇B, g1, f, t1, t2, u, t3, _hM9, hp5, hf,
      ht1, ht2, hu, ht3, _hq1, _hq2, _hD0, _hE, _hF0, _hG, _hI0, _hJ,
      _hL0⟩ := hpacket9
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hpin1 : 3 * f.eval a = g1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = g1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2pin : 81 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) hu
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have ht2pin : t2.eval a = 6 * g1.eval a * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht3
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2ref : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a ^ 2 * t1.eval a := by
      linear_combination (3⁻¹ : K) * hp2pin +
        (3⁻¹ : K) * g1.eval a * ht2pin
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, t1, t2, u, t3, hp5, hf, ht1, ht2, hu, ht3, hpin1,
        hpin2, hp2pin, ht2pin, hp2ref⟩⟩
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

#print axioms alignedNinthCoefficientJacobianRow_610
#print axioms alignedNinthDefect_weightedDerivative_identity_610
#print axioms alignedNinthDefectRow_eq_zero_610
#print axioms alignedNinthDefectPowerRelation_610
#print axioms alignedSquareNinth_sqrt_610
#print axioms alignedNinthSquareResolve_610
#print axioms alignedSquareNinth_descent_610
#print axioms alignedNonsquareNinth_defect_eq_zero_610
#print axioms alignedNonsquareNinth_descent_610
#print axioms normalized610ScaleTwo_alignedNinthFace_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedNinthFace_rootData

end Max11DegreeRoutes
