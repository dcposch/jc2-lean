import Fable610ScaleTwoAlignedSeventhFaceScratch

/-! # Eighth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedSeventhFaceScratch` consumed the degree-`8`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
squared weight-thirty-five integral `I² = κ₆ H³⁵`, resolving the
sixth-face sextic tie into the exact root pins `3 f₂(a) = w₁(a)²`,
`27 p₃(a) = w₁(a)³` and the divisibilities `3 f₂ - w₁² = h₀ e₁`,
`27 p₃ - w₁³ = h₀ e₂` (square chamber; `t₁, t₂` against `H` in the
nonsquare chamber).  This file consumes the next unused aligned row,
the degree-`7` Jacobian coefficient — the first row that sees `q₂`
(pairs `(0,8), (1,7), (2,6), (3,5), (4,4), (5,3), (6,2)`).

At the source level, modulo the face and the consumed degree-`13`
through degree-`8` rows, the degree-`7` row is the weighted derivative
of the cleared eighth defect

`J = 16796160 (p₀ p₄ + p₁ p₃) H¹⁸ + 8398080 p₂² H¹⁸ - 15116544 q₂ H¹⁹
  - 2799360 p₀ p₅² H¹⁵ - 5598720 (p₁ p₄ + p₂ p₃) p₅ H¹⁵
  - 2799360 (p₂ p₄² + p₃² p₄) H¹⁵ + partitions-of-8 monomials
  + κ-block - (217728 p₁ H¹² + 36288 (p₂ p₅ + p₃ p₄) H⁹
  - 15120 (p₃ p₅² + p₄² p₅) H⁶ + 9240 p₄ p₅³ H³ - 1309 p₅⁵) D
  - 31104 p₂ H⁹ E - (2160 p₃ H⁶ - 360 p₄ p₅ H³ + 70 p₅³) F
  - (96 p₄ H³ - 16 p₅²) G - 3 p₅ I`,

kept in factored form through the third–seventh defects, via the exact
multiplier identity

`2519424 H¹⁷ · row₇[p₆ = H³] = (H J' - 20 J H') + 2239488 H¹⁶ p₀' C
  + (124416 p₁ H¹² + 145152 (p₂ p₅ + p₃ p₄) H⁹
     + 12096 (p₃ p₅² + p₄² p₅) H⁶ - 3360 p₄ p₅³ H³ + 308 p₅⁵) rowD
  + (41472 (p₂ H³ + p₃ p₅) H⁶ + 20736 p₄² H⁶) rowE
  + (1728 p₃ H⁶ + 1440 p₄ p₅ H³ - 40 p₅³) rowF
  + (192 p₄ H³ + 64 p₅²) rowG + 4 p₅ rowI`

(the row has no `q₉` at all, so there is no `N`-correction, and `q₈`
enters only through `p₀'`, so the `C`-correction needs neither `C'`
nor an `H'`-mate).  On the aligned face every correction vanishes, so
`H J' = 20 J H'` and the weight-twenty first integral `J = κ₇ H²⁰`
holds for a preserved constant `κ₇` in BOTH chambers (even exponent,
chamber-free like `E` and `G`).

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `E = κ₃ H¹⁰`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`,
  `I = ν₂ h₀³⁵`): cancelling `h₀³²` leaves the chamber core whose
  `h₀`-free octic head is
  `1280 (α² z² - α² β + 12 α β² z - 6 α β z³ + 3 β⁴ - 30 β³ z² + 9 β² z⁴)`
  in `α = 27 p₃ - w₁³`, `β = 3 f₂ - w₁²`, `z = w₁` — absorbed by the
  seventh-face divisibilities.  Substituting `e₁, e₂` peels `h₀²` more:
  the peeled row has head `1280 w₁² (e₂ - 3 e₁ w₁)²` and `q₂` tied at
  `h₀⁴`, giving the NEW product divisibility
  `w₁ (e₂ - 3 e₁ w₁) = h₀ u₂`.  COMBINED with the seventh-face peeled
  relation (`+ 2 w₁ ·`), one more `h₀` peels and the combined row
  `= κ₇ h₀⁵ + 2 ν₂ w₁ h₀⁴` has head
  `-1280 e₁ (3 e₁ w₁ - e₂)(6 e₁ w₁ - e₂) - 189 μ w₁⁵`.  At the root
  the seventh-face residual branch is REFINED:
  `(w₁(a) = 0 ∧ (e₁(a) = 0 ∨ e₂(a) = 0)) ∨`
  `(e₂(a) = 3 e₁(a) w₁(a) ∧ (μ = 0 ∨ w₁(a) = 0))`.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `I = 0`, `E = κ₃ H¹⁰`,
  `G = κ₅ H¹⁵`): cancelling `H¹⁶` and substituting `t₁, t₂` peels `H²`
  with PERFECT-SQUARE head `1280 (81 p₂ + 3 g₁² t₁ - g₁ t₂)²`, which
  vanishes at BOTH simple roots and transfers to the NEW divisibility
  `81 p₂ + 3 g₁² t₁ - g₁ t₂ = H u` — the first constraint on `p₂` in
  the aligned tower, pinning `81 p₂(a) = g₁(a) t₂(a) - 3 g₁(a)² t₁(a)`
  at every root.  Substituting `u` peels one more `H` and `q₂` is
  solved OUTRIGHT:
  `15116544 q₂ = 2799360 g₁² p₀ - 26880 g₁² t₁³ - 1866240 g₁ p₁ t₁
  + 11520 g₁ t₁² t₂ + 622080 p₁ t₂ - 1280 t₁ t₂² + κ(…) + κ₃(…)
  - 16 κ₅ g₁² + H (…) - κ₇ H`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `u₂ = 0`, `g₁ = 0`, `f = 0`,
`t₁ = 0`, `t₂ = 0`, `u = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `ν = 0`,
`κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`, `κ₇ = 0`) are not excluded, and the
constants `κ`, `κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²`, `κ₇` are
preserved where not forced.  The refined square residual branch keeps
both alternatives; no individual vanishing of `p₀, p₁, p₂, p₃, q₂, q₃`
is claimed.  The next unused Keller row on the aligned face is the
degree-`6` Jacobian coefficient, the first row that sees `q₁` (pairs
`(0,7), (1,6), (2,5), (3,4), (4,3), (5,2), (6,1)`; expected
weight-`45/2` defect, odd exponent, chambered like `D`, `F`, `I`).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`7` Keller coefficient on the aligned face -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`7` Jacobian coefficient, the first
aligned row that sees `q₂`. -/
theorem alignedEighthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
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
        (7, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8]
  linear_combination hcoeff

/-! ## Aligned eighth defect -/

/-- Cleared eighth defect of the degree-`7` aligned `(6,10)` row, kept
in factored form through the third defect `D`, the fourth defect `E`,
the fifth defect `F`, the sixth defect `G`, and the seventh defect `I`.
On the aligned face it is a polynomial first integral of weight
twenty. -/
def alignedEighthDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (16796160 : K[X]) * a0 * a4 * H ^ 18 +
    (16796160 : K[X]) * a1 * a3 * H ^ 18 +
    (8398080 : K[X]) * a2 ^ 2 * H ^ 18 -
    (15116544 : K[X]) * b2 * H ^ 19 -
    (2799360 : K[X]) * a0 * a5 ^ 2 * H ^ 15 -
    (5598720 : K[X]) * a1 * a4 * a5 * H ^ 15 -
    (5598720 : K[X]) * a2 * a3 * a5 * H ^ 15 -
    (2799360 : K[X]) * a2 * a4 ^ 2 * H ^ 15 -
    (2799360 : K[X]) * a3 ^ 2 * a4 * H ^ 15 +
    (1244160 : K[X]) * a1 * a5 ^ 3 * H ^ 12 +
    (3732480 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 +
    (1866240 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 +
    (3732480 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 12 +
    (311040 : K[X]) * a4 ^ 4 * H ^ 12 -
    (725760 : K[X]) * a2 * a5 ^ 4 * H ^ 9 -
    (2903040 : K[X]) * a3 * a4 * a5 ^ 3 * H ^ 9 -
    (1451520 : K[X]) * a4 ^ 3 * a5 ^ 2 * H ^ 9 +
    (483840 : K[X]) * a3 * a5 ^ 5 * H ^ 6 +
    (1209600 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 -
    (349440 : K[X]) * a4 * a5 ^ 6 * H ^ 3 + (33280 : K[X]) * a5 ^ 8 +
    Polynomial.C κ *
      ((2239488 : K[X]) * a0 * H ^ 20 +
        (746496 : K[X]) * a1 * a5 * H ^ 17 +
        (746496 : K[X]) * a2 * a4 * H ^ 17 +
        (373248 : K[X]) * a3 ^ 2 * H ^ 17 -
        (248832 : K[X]) * a2 * a5 ^ 2 * H ^ 14 -
        (497664 : K[X]) * a3 * a4 * a5 * H ^ 14 -
        (82944 : K[X]) * a4 ^ 3 * H ^ 14 +
        (138240 : K[X]) * a3 * a5 ^ 3 * H ^ 11 +
        (207360 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 11 -
        (92160 : K[X]) * a4 * a5 ^ 4 * H ^ 8 +
        (11264 : K[X]) * a5 ^ 6 * H ^ 5) -
    ((217728 : K[X]) * a1 * H ^ 12 + (36288 : K[X]) * a2 * a5 * H ^ 9 +
        (36288 : K[X]) * a3 * a4 * H ^ 9 -
        (15120 : K[X]) * a3 * a5 ^ 2 * H ^ 6 -
        (15120 : K[X]) * a4 ^ 2 * a5 * H ^ 6 +
        (9240 : K[X]) * a4 * a5 ^ 3 * H ^ 3 -
        (1309 : K[X]) * a5 ^ 5) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ -
    (31104 : K[X]) * a2 * H ^ 9 *
      alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ -
    ((2160 : K[X]) * a3 * H ^ 6 - (360 : K[X]) * a4 * a5 * H ^ 3 +
        (70 : K[X]) * a5 ^ 3) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ -
    ((96 : K[X]) * a4 * H ^ 3 - (16 : K[X]) * a5 ^ 2) *
      alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ -
    (3 : K[X]) * a5 *
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ

set_option maxHeartbeats 3200000000 in
/-- Exact combination of the degree-`7` Jacobian expression with the
weighted derivative of `J`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`8` rows.  The row has no `q₉` term at all, so there is no
`N`-correction, and no `q₈`-derivative term, so the `C`-correction
carries neither `C'` nor an `H'`-mate. -/
theorem alignedEighthDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 b8 : K[X]) (κ : K) :
    (2519424 : K[X]) * H ^ 17 *
        ((H ^ 3).derivative * (b2 * (2 : K[X])) +
          a5.derivative * (b3 * (3 : K[X])) +
          a4.derivative * (b4 * (4 : K[X])) +
          a3.derivative * (b5 * (5 : K[X])) +
          a2.derivative * (b6 * (6 : K[X])) +
          a1.derivative * (b7 * (7 : K[X])) +
          a0.derivative * (b8 * (8 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b2.derivative +
          (a5 * (5 : K[X])) * b3.derivative +
          (a4 * (4 : K[X])) * b4.derivative +
          (a3 * (3 : K[X])) * b5.derivative +
          (a2 * (2 : K[X])) * b6.derivative +
          a1 * b7.derivative)) =
      (H *
          (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
            κ).derivative -
        (20 : K[X]) *
          alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ *
          H.derivative) +
        (2239488 : K[X]) * H ^ 16 * a0.derivative *
          ((9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
            (5 : K[X]) * a5 ^ 2 - Polynomial.C κ * H ^ 5) +
        ((124416 : K[X]) * a1 * H ^ 12 +
            (145152 : K[X]) * a2 * a5 * H ^ 9 +
            (145152 : K[X]) * a3 * a4 * H ^ 9 +
            (12096 : K[X]) * a3 * a5 ^ 2 * H ^ 6 +
            (12096 : K[X]) * a4 ^ 2 * a5 * H ^ 6 -
            (3360 : K[X]) * a4 * a5 ^ 3 * H ^ 3 +
            (308 : K[X]) * a5 ^ 5) *
          ((2 : K[X]) * H *
              (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative -
            (15 : K[X]) * alignedThirdDefect610 H a3 a4 a5 b7 κ *
              H.derivative) +
        ((41472 : K[X]) * a2 * H ^ 9 + (41472 : K[X]) * a3 * a5 * H ^ 6 +
            (20736 : K[X]) * a4 ^ 2 * H ^ 6) *
          (H * (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative -
            (10 : K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ *
              H.derivative) +
        ((1728 : K[X]) * a3 * H ^ 6 + (1440 : K[X]) * a4 * a5 * H ^ 3 -
            (40 : K[X]) * a5 ^ 3) *
          ((2 : K[X]) * H *
              (alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7
                κ).derivative -
            (25 : K[X]) *
              alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ *
              H.derivative) +
        ((192 : K[X]) * a4 * H ^ 3 + (64 : K[X]) * a5 ^ 2) *
          (H *
              (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7
                κ).derivative -
            (15 : K[X]) *
              alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ *
              H.derivative) +
        (4 : K[X]) * a5 *
          ((2 : K[X]) * H *
              (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
                κ).derivative -
            (35 : K[X]) *
              alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
                κ *
              H.derivative) := by
  simp only [alignedEighthDefect610, alignedSeventhDefect610,
    alignedSixthDefect610, alignedFifthDefect610, alignedFourthDefect610,
    alignedThirdDefect610, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add,
    add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`8` rows, the degree-`7` row is the weighted derivative
`H J' - 20 J H' = 0`. -/
theorem alignedEighthDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    H *
        (alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (20 : K[X]) *
        alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedEighthCoefficientJacobianRow_610 hp hq hjac
  rw [hp6] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8] at hrow
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
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedEighthDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) (q.coeff 8) κ
  rw [hrow, hC0, hDrow, hErow, hFrow, hGrow, hIrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-twenty polynomial first integral of the aligned `(6,10)`
eighth defect: `J = κ₇ H²⁰`.  The even exponent makes the integral
chamber-free — no square root of `H` is required and `κ₇` is preserved
in both chambers. -/
theorem alignedEighthDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₇ : K,
      alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₇ * H ^ 20 := by
  let J : K[X] :=
    alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow : H * J.derivative - (20 : K[X]) * J * H.derivative = 0 := by
    simpa only [J] using
      alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC20 : Polynomial.C (20 : K) = (20 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian J (H ^ 20) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      J * (Polynomial.C (20 : K) * H ^ (20 - 1) * H.derivative) -
          J.derivative * H ^ 20 =
          H ^ 19 *
            (Polynomial.C (20 : K) * J * H.derivative -
              H * J.derivative) := by
        ring
      _ = 0 := by
        rw [hC20]
        have hfac :
            (20 : K[X]) * J * H.derivative - H * J.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 20 hH) hW

/-! ## Square chamber -/

/-- Twice-peeled square-chamber form of the consumed degree-`7` row
(`h₀³² · h₀²` cancelled): head `1280 w₁² (e₂ - 3 e₁ w₁)²`, `q₂` tied at
`h₀⁴`.  On the face it equals `κ₇ h₀⁶`. -/
def alignedEighthSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 a0 a1 a2 b2 : K[X]) (κ μ κ₃ ν κ₅ ν₂ : K) : K[X] :=
  (1280 : K[X]) * w1 ^ 2 * (e2 - (3 : K[X]) * e1 * w1) ^ 2 +
    h0 * ((15360 : K[X]) * e1 ^ 2 * e2 * w1 -
      (38400 : K[X]) * e1 ^ 3 * w1 ^ 2 - (1280 : K[X]) * e1 * e2 ^ 2 +
      (622080 : K[X]) * e1 * a2 * w1 ^ 2 -
      (207360 : K[X]) * e2 * a2 * w1 +
      Polynomial.C μ * ((21 : K[X]) * w1 ^ 5)) +
    h0 ^ 2 * ((3840 : K[X]) * e1 ^ 4 - (311040 : K[X]) * e1 ^ 2 * a2 +
      (8398080 : K[X]) * a2 ^ 2 +
      Polynomial.C κ * ((13824 : K[X]) * e1 ^ 2 * w1 ^ 2 -
        (6144 : K[X]) * e1 * e2 * w1 + (512 : K[X]) * e2 ^ 2) +
      Polynomial.C μ * ((112 : K[X]) * e2 * w1 ^ 2 -
        (168 : K[X]) * e1 * w1 ^ 3)) +
    h0 ^ 3 * ((622080 : K[X]) * e2 * a1 -
      (1866240 : K[X]) * e1 * a1 * w1 +
      Polynomial.C κ * ((248832 : K[X]) * e1 * a2 -
        (3072 : K[X]) * e1 ^ 3) +
      Polynomial.C μ * ((1680 : K[X]) * e1 ^ 2 * w1 -
        (448 : K[X]) * e1 * e2 - (36288 : K[X]) * a2 * w1) -
      Polynomial.C ν * ((30 : K[X]) * w1 ^ 3)) +
    h0 ^ 4 * ((2799360 : K[X]) * a0 * w1 ^ 2 - (15116544 : K[X]) * b2 +
      Polynomial.C κ * ((746496 : K[X]) * a1 * w1) +
      Polynomial.C ν * ((120 : K[X]) * e1 * w1 - (80 : K[X]) * e2) -
      Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
      Polynomial.C κ₅ * ((16 : K[X]) * w1 ^ 2)) +
    h0 ^ 5 * ((5598720 : K[X]) * e1 * a0 -
      Polynomial.C μ * ((217728 : K[X]) * a1) -
      Polynomial.C κ₅ * ((32 : K[X]) * e1) -
      Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
    h0 ^ 6 * (Polynomial.C κ * ((2239488 : K[X]) * a0))

/-- Combined square-chamber row: the peeled eighth row plus `2 w₁`
times the seventh-face peeled relation, with one more `h₀` cancelled.
Head `-1280 e₁ (3 e₁ w₁ - e₂)(6 e₁ w₁ - e₂) - 189 μ w₁⁵`; on the face
it equals `κ₇ h₀⁵ + 2 ν₂ w₁ h₀⁴`. -/
def alignedEighthSquareCombinedRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 a0 a1 a2 b2 b3 : K[X]) (κ μ κ₃ ν κ₅ ν₂ : K) : K[X] :=
  (-(1280 : K[X])) * e1 * ((3 : K[X]) * e1 * w1 - e2) *
      ((6 : K[X]) * e1 * w1 - e2) -
    Polynomial.C μ * ((189 : K[X]) * w1 ^ 5) +
    h0 * ((3840 : K[X]) * e1 ^ 4 - (311040 : K[X]) * e1 ^ 2 * a2 +
      (933120 : K[X]) * a1 * w1 ^ 3 + (8398080 : K[X]) * a2 ^ 2 -
      (5038848 : K[X]) * b3 * w1 +
      Polynomial.C κ * ((4608 : K[X]) * e1 ^ 2 * w1 ^ 2 -
        (3072 : K[X]) * e1 * e2 * w1 + (512 : K[X]) * e2 ^ 2 +
        (248832 : K[X]) * a2 * w1 ^ 2) +
      Polynomial.C μ * ((168 : K[X]) * e1 * w1 ^ 3 -
        (336 : K[X]) * e2 * w1 ^ 2) -
      Polynomial.C κ₃ * ((384 : K[X]) * w1 ^ 4)) +
    h0 ^ 2 * ((622080 : K[X]) * e2 * a1 +
      Polynomial.C κ * ((248832 : K[X]) * e1 * a2 -
        (3072 : K[X]) * e1 ^ 3) +
      Polynomial.C μ * ((1008 : K[X]) * e1 ^ 2 * w1 -
        (448 : K[X]) * e1 * e2 - (108864 : K[X]) * a2 * w1) -
      Polynomial.C κ₃ * ((384 : K[X]) * e2 * w1) -
      Polynomial.C ν * ((210 : K[X]) * w1 ^ 3)) +
    h0 ^ 3 * ((8398080 : K[X]) * a0 * w1 ^ 2 - (15116544 : K[X]) * b2 +
      Polynomial.C κ * ((1492992 : K[X]) * a1 * w1) -
      Polynomial.C ν * ((120 : K[X]) * e1 * w1 + (80 : K[X]) * e2) -
      Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
      Polynomial.C κ₅ * ((48 : K[X]) * w1 ^ 2)) +
    h0 ^ 4 * ((5598720 : K[X]) * e1 * a0 -
      Polynomial.C μ * ((217728 : K[X]) * a1) -
      Polynomial.C κ₅ * ((32 : K[X]) * e1) -
      Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
    h0 ^ 5 * (Polynomial.C κ * ((2239488 : K[X]) * a0))

set_option maxHeartbeats 3200000000 in
/-- Descent of the consumed degree-`7` row in the square chamber: the
`h₀³²`-peeled core absorbs the octic head through the seventh-face
divisibilities, cancelling `h₀²` more leaves the peeled row with head
`1280 w₁² (e₂ - 3 e₁ w₁)²` and `q₂` tied at `h₀⁴`, the root of `h₀`
transfers to the NEW product divisibility `w₁ (e₂ - 3 e₁ w₁) = h₀ u₂`,
and adding `2 w₁` times the seventh-face peeled relation cancels one
more `h₀` into the combined row `= κ₇ h₀⁵ + 2 ν₂ w₁ h₀⁴`. -/
theorem alignedSquareEighth_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ : K}
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
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hR7 : (-(640 : K[X])) * w1 * (e2 - (3 : K[X]) * e1 * w1) ^ 2 +
          h0 * ((7680 : K[X]) * e1 ^ 3 * w1 -
            (1920 : K[X]) * e1 ^ 2 * e2 -
            (311040 : K[X]) * e1 * a2 * w1 + (103680 : K[X]) * e2 * a2 -
            Polynomial.C μ * ((105 : K[X]) * w1 ^ 4)) +
          h0 ^ 2 * ((466560 : K[X]) * a1 * w1 ^ 2 -
            (2519424 : K[X]) * b3 +
            Polynomial.C κ * ((1536 : K[X]) * e1 * e2 -
              (4608 : K[X]) * e1 ^ 2 * w1 + (124416 : K[X]) * a2 * w1) +
            Polynomial.C μ * ((168 : K[X]) * e1 * w1 ^ 2 -
              (224 : K[X]) * e2 * w1) -
            Polynomial.C κ₃ * ((192 : K[X]) * w1 ^ 3)) +
          h0 ^ 3 * ((933120 : K[X]) * e1 * a1 -
            Polynomial.C μ * ((336 : K[X]) * e1 ^ 2 +
              (36288 : K[X]) * a2) -
            Polynomial.C κ₃ * ((192 : K[X]) * e2) -
            Polynomial.C ν * ((90 : K[X]) * w1 ^ 2)) +
          h0 ^ 4 * ((2799360 : K[X]) * a0 * w1 +
            Polynomial.C κ * ((373248 : K[X]) * a1) -
            Polynomial.C ν * ((120 : K[X]) * e1) -
            Polynomial.C κ₅ * ((16 : K[X]) * w1)) =
        Polynomial.C ν₂ * h0 ^ 5) :
    ∃ u2 : K[X],
      w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
      alignedEighthSquarePeeledRow610 h0 w1 e1 e2 a0 a1 a2 b2
          κ μ κ₃ ν κ₅ ν₂ = Polynomial.C κ₇ * h0 ^ 6 ∧
      alignedEighthSquareCombinedRow610 h0 w1 e1 e2 a0 a1 a2 b2 b3
          κ μ κ₃ ν κ₅ ν₂ =
        Polynomial.C κ₇ * h0 ^ 5 +
          Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) := by
  have hcore :
      (311040 : K[X]) * f2 ^ 4 - (1451520 : K[X]) * f2 ^ 3 * w1 ^ 2 +
          (3732480 : K[X]) * f2 ^ 2 * a3 * w1 +
          (1209600 : K[X]) * f2 ^ 2 * w1 ^ 4 -
          (2799360 : K[X]) * f2 * a3 ^ 2 -
          (2903040 : K[X]) * f2 * a3 * w1 ^ 3 -
          (349440 : K[X]) * f2 * w1 ^ 6 +
          (1866240 : K[X]) * a3 ^ 2 * w1 ^ 2 +
          (483840 : K[X]) * a3 * w1 ^ 5 + (33280 : K[X]) * w1 ^ 8 +
          h0 ^ 2 * (Polynomial.C κ * ((373248 : K[X]) * a3 ^ 2 +
              (138240 : K[X]) * a3 * w1 ^ 3 + (11264 : K[X]) * w1 ^ 6 -
              (82944 : K[X]) * f2 ^ 3 +
              (207360 : K[X]) * f2 ^ 2 * w1 ^ 2 -
              (497664 : K[X]) * f2 * a3 * w1 -
              (92160 : K[X]) * f2 * w1 ^ 4) -
            (2799360 : K[X]) * f2 ^ 2 * a2 +
            (3732480 : K[X]) * f2 * a2 * w1 ^ 2 -
            (5598720 : K[X]) * a2 * a3 * w1 -
            (725760 : K[X]) * a2 * w1 ^ 4) +
          h0 ^ 3 * (Polynomial.C μ * ((15120 : K[X]) * f2 ^ 2 * w1 -
            (36288 : K[X]) * f2 * a3 - (9240 : K[X]) * f2 * w1 ^ 3 +
            (15120 : K[X]) * a3 * w1 ^ 2 + (1309 : K[X]) * w1 ^ 5)) +
          h0 ^ 4 * (Polynomial.C κ * ((746496 : K[X]) * f2 * a2 -
              (248832 : K[X]) * a2 * w1 ^ 2) -
            (5598720 : K[X]) * f2 * a1 * w1 +
            (16796160 : K[X]) * a1 * a3 +
            (1244160 : K[X]) * a1 * w1 ^ 3 +
            (8398080 : K[X]) * a2 ^ 2) +
          h0 ^ 5 * (Polynomial.C ν * ((360 : K[X]) * f2 * w1 -
              (2160 : K[X]) * a3 - (70 : K[X]) * w1 ^ 3) -
            Polynomial.C μ * ((36288 : K[X]) * a2 * w1)) +
          h0 ^ 6 * ((16796160 : K[X]) * f2 * a0 -
            (2799360 : K[X]) * a0 * w1 ^ 2 - (15116544 : K[X]) * b2 +
            Polynomial.C κ * ((746496 : K[X]) * a1 * w1) -
            Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
            Polynomial.C κ₅ * ((96 : K[X]) * f2 -
              (16 : K[X]) * w1 ^ 2)) +
          h0 ^ 7 * (-(Polynomial.C μ * ((217728 : K[X]) * a1)) -
            Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
          h0 ^ 8 * (Polynomial.C κ * ((2239488 : K[X]) * a0)) =
        Polynomial.C κ₇ * h0 ^ 8 := by
    have hJ' := hJ
    simp only [alignedEighthDefect610] at hJ'
    rw [hD, hE, hF, hG, hI, hHsq, hp5, hp4] at hJ'
    apply mul_left_cancel₀ (pow_ne_zero 32 hh0)
    linear_combination hJ'
  have hR8 :
      (1280 : K[X]) * w1 ^ 2 * (e2 - (3 : K[X]) * e1 * w1) ^ 2 +
          h0 * ((15360 : K[X]) * e1 ^ 2 * e2 * w1 -
            (38400 : K[X]) * e1 ^ 3 * w1 ^ 2 -
            (1280 : K[X]) * e1 * e2 ^ 2 +
            (622080 : K[X]) * e1 * a2 * w1 ^ 2 -
            (207360 : K[X]) * e2 * a2 * w1 +
            Polynomial.C μ * ((21 : K[X]) * w1 ^ 5)) +
          h0 ^ 2 * ((3840 : K[X]) * e1 ^ 4 -
            (311040 : K[X]) * e1 ^ 2 * a2 +
            (8398080 : K[X]) * a2 ^ 2 +
            Polynomial.C κ * ((13824 : K[X]) * e1 ^ 2 * w1 ^ 2 -
              (6144 : K[X]) * e1 * e2 * w1 + (512 : K[X]) * e2 ^ 2) +
            Polynomial.C μ * ((112 : K[X]) * e2 * w1 ^ 2 -
              (168 : K[X]) * e1 * w1 ^ 3)) +
          h0 ^ 3 * ((622080 : K[X]) * e2 * a1 -
            (1866240 : K[X]) * e1 * a1 * w1 +
            Polynomial.C κ * ((248832 : K[X]) * e1 * a2 -
              (3072 : K[X]) * e1 ^ 3) +
            Polynomial.C μ * ((1680 : K[X]) * e1 ^ 2 * w1 -
              (448 : K[X]) * e1 * e2 - (36288 : K[X]) * a2 * w1) -
            Polynomial.C ν * ((30 : K[X]) * w1 ^ 3)) +
          h0 ^ 4 * ((2799360 : K[X]) * a0 * w1 ^ 2 -
            (15116544 : K[X]) * b2 +
            Polynomial.C κ * ((746496 : K[X]) * a1 * w1) +
            Polynomial.C ν * ((120 : K[X]) * e1 * w1 -
              (80 : K[X]) * e2) -
            Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
            Polynomial.C κ₅ * ((16 : K[X]) * w1 ^ 2)) +
          h0 ^ 5 * ((5598720 : K[X]) * e1 * a0 -
            Polynomial.C μ * ((217728 : K[X]) * a1) -
            Polynomial.C κ₅ * ((32 : K[X]) * e1) -
            Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
          h0 ^ 6 * (Polynomial.C κ * ((2239488 : K[X]) * a0)) =
        Polynomial.C κ₇ * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    linear_combination hcore +
      ((3840 : K[X]) * e2 * f2 * h0 - (2560 : K[X]) * e2 * h0 * w1 ^ 2 -
        (138240 : K[X]) * f2 ^ 2 * w1 + (103680 : K[X]) * f2 * a3 +
        (111360 : K[X]) * f2 * w1 ^ 3 - (622080 : K[X]) * h0 ^ 4 * a1 +
        (207360 : K[X]) * h0 ^ 2 * a2 * w1 -
        (69120 : K[X]) * a3 * w1 ^ 2 - (20480 : K[X]) * w1 ^ 5 +
        Polynomial.C κ * ((18432 : K[X]) * f2 * h0 ^ 2 * w1 -
          (512 : K[X]) * e2 * h0 ^ 3 - (13824 : K[X]) * h0 ^ 2 * a3 -
          (5632 : K[X]) * h0 ^ 2 * w1 ^ 3) +
        Polynomial.C μ * ((1344 : K[X]) * f2 * h0 ^ 3 -
          (560 : K[X]) * h0 ^ 3 * w1 ^ 2) +
        Polynomial.C ν * ((80 : K[X]) * h0 ^ 5)) * he2 +
      (-((3840 : K[X]) * e1 ^ 3 * h0 ^ 3) -
        (11520 : K[X]) * e1 ^ 2 * f2 * h0 ^ 2 +
        (42240 : K[X]) * e1 ^ 2 * h0 ^ 2 * w1 ^ 2 -
        (15360 : K[X]) * e1 * e2 * h0 ^ 2 * w1 -
        (34560 : K[X]) * e1 * f2 ^ 2 * h0 +
        (138240 : K[X]) * e1 * f2 * h0 * w1 ^ 2 +
        (311040 : K[X]) * e1 * h0 ^ 3 * a2 -
        (53760 : K[X]) * e1 * h0 * w1 ^ 4 +
        (1280 : K[X]) * e2 ^ 2 * h0 ^ 2 -
        (46080 : K[X]) * e2 * f2 * h0 * w1 +
        (23040 : K[X]) * e2 * h0 * w1 ^ 3 - (103680 : K[X]) * f2 ^ 3 +
        (449280 : K[X]) * f2 ^ 2 * w1 ^ 2 +
        (933120 : K[X]) * f2 * h0 ^ 2 * a2 -
        (299520 : K[X]) * f2 * w1 ^ 4 - (5598720 : K[X]) * h0 ^ 6 * a0 +
        (1866240 : K[X]) * h0 ^ 4 * a1 * w1 -
        (933120 : K[X]) * h0 ^ 2 * a2 * w1 ^ 2 +
        (53760 : K[X]) * w1 ^ 6 +
        Polynomial.C κ * ((3072 : K[X]) * e1 ^ 2 * h0 ^ 4 +
          (9216 : K[X]) * e1 * f2 * h0 ^ 3 -
          (16896 : K[X]) * e1 * h0 ^ 3 * w1 ^ 2 +
          (6144 : K[X]) * e2 * h0 ^ 3 * w1 +
          (27648 : K[X]) * f2 ^ 2 * h0 ^ 2 -
          (59904 : K[X]) * f2 * h0 ^ 2 * w1 ^ 2 -
          (248832 : K[X]) * h0 ^ 4 * a2 +
          (16896 : K[X]) * h0 ^ 2 * w1 ^ 4) +
        Polynomial.C μ * ((448 : K[X]) * e2 * h0 ^ 4 -
          (1680 : K[X]) * e1 * h0 ^ 4 * w1 -
          (5040 : K[X]) * f2 * h0 ^ 3 * w1 +
          (1848 : K[X]) * h0 ^ 3 * w1 ^ 3) +
        Polynomial.C κ₅ * ((32 : K[X]) * h0 ^ 6) -
        Polynomial.C ν * ((120 : K[X]) * h0 ^ 5 * w1)) * he1
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hR8
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have hsq :
      ((w1 * (e2 - (3 : K[X]) * e1 * w1)).eval (-(d / c))) ^ 2 = 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_ofNat]
    linear_combination ((1280 : K)⁻¹) * hev
  have hzero := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  obtain ⟨u2, hu2⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    (w1 * (e2 - (3 : K[X]) * e1 * w1)) (-(d / c)) hdeg1 hroot hzero
  have hQ9 :
      (-(1280 : K[X])) * e1 * ((3 : K[X]) * e1 * w1 - e2) *
          ((6 : K[X]) * e1 * w1 - e2) -
        Polynomial.C μ * ((189 : K[X]) * w1 ^ 5) +
        h0 * ((3840 : K[X]) * e1 ^ 4 - (311040 : K[X]) * e1 ^ 2 * a2 +
          (933120 : K[X]) * a1 * w1 ^ 3 + (8398080 : K[X]) * a2 ^ 2 -
          (5038848 : K[X]) * b3 * w1 +
          Polynomial.C κ * ((4608 : K[X]) * e1 ^ 2 * w1 ^ 2 -
            (3072 : K[X]) * e1 * e2 * w1 + (512 : K[X]) * e2 ^ 2 +
            (248832 : K[X]) * a2 * w1 ^ 2) +
          Polynomial.C μ * ((168 : K[X]) * e1 * w1 ^ 3 -
            (336 : K[X]) * e2 * w1 ^ 2) -
          Polynomial.C κ₃ * ((384 : K[X]) * w1 ^ 4)) +
        h0 ^ 2 * ((622080 : K[X]) * e2 * a1 +
          Polynomial.C κ * ((248832 : K[X]) * e1 * a2 -
            (3072 : K[X]) * e1 ^ 3) +
          Polynomial.C μ * ((1008 : K[X]) * e1 ^ 2 * w1 -
            (448 : K[X]) * e1 * e2 - (108864 : K[X]) * a2 * w1) -
          Polynomial.C κ₃ * ((384 : K[X]) * e2 * w1) -
          Polynomial.C ν * ((210 : K[X]) * w1 ^ 3)) +
        h0 ^ 3 * ((8398080 : K[X]) * a0 * w1 ^ 2 -
          (15116544 : K[X]) * b2 +
          Polynomial.C κ * ((1492992 : K[X]) * a1 * w1) -
          Polynomial.C ν * ((120 : K[X]) * e1 * w1 + (80 : K[X]) * e2) -
          Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
          Polynomial.C κ₅ * ((48 : K[X]) * w1 ^ 2)) +
        h0 ^ 4 * ((5598720 : K[X]) * e1 * a0 -
          Polynomial.C μ * ((217728 : K[X]) * a1) -
          Polynomial.C κ₅ * ((32 : K[X]) * e1) -
          Polynomial.C ν₂ * ((3 : K[X]) * w1)) +
        h0 ^ 5 * (Polynomial.C κ * ((2239488 : K[X]) * a0)) =
        Polynomial.C κ₇ * h0 ^ 5 +
          Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) := by
    apply mul_left_cancel₀ hh0
    linear_combination hR8 + ((2 : K[X]) * w1) * hR7
  refine ⟨u2, hu2, ?_, ?_⟩
  · simp only [alignedEighthSquarePeeledRow610]
    linear_combination hR8
  · simp only [alignedEighthSquareCombinedRow610]
    linear_combination hQ9

/-- Scalar resolution of the combined square-chamber head against the
peeled-row head at the root: `x (v - 3 u x) = 0` together with
`1280 u (3 u x - v)(6 u x - v) + 189 m x⁵ = 0` refines the seventh-face
residual branch — on the `x = 0` branch it forces `u = 0 ∨ v = 0`, and
on the `v = 3 u x` branch it forces `m = 0 ∨ x = 0`. -/
theorem alignedEighthCombinedResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : 1280 * u * (3 * u * x - v) * (6 * u * x - v) +
      189 * m * x ^ 5 = 0) :
    (x = 0 ∧ (u = 0 ∨ v = 0)) ∨ (v = 3 * u * x ∧ (m = 0 ∨ x = 0)) := by
  rcases mul_eq_zero.mp h1 with hx | hv
  · refine Or.inl ⟨hx, ?_⟩
    have h3 : (1280 : K) * (u * v ^ 2) = 0 := by
      rw [hx] at h2
      linear_combination h2
    have h4 : u * v ^ 2 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num : (1280 : K) ≠ 0)
    rcases mul_eq_zero.mp h4 with hu | hv2
    · exact Or.inl hu
    · exact Or.inr ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hv2)
  · have hv' : v = 3 * u * x := by linear_combination hv
    refine Or.inr ⟨hv', ?_⟩
    have h5 : (189 : K) * (m * x ^ 5) = 0 := by
      linear_combination h2 + (1280 * u * (6 * u * x - v)) * hv
    have h6 : m * x ^ 5 = 0 :=
      (mul_eq_zero.mp h5).resolve_left (by norm_num : (189 : K) ≠ 0)
    rcases mul_eq_zero.mp h6 with hm | hx5
    · exact Or.inl hm
    · exact Or.inr ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hx5)

/-! ## Nonsquare chamber -/

/-- Twice-peeled nonsquare-chamber form of the consumed degree-`7` row
(`H¹⁶ · H²` cancelled): PERFECT-SQUARE head
`1280 (81 p₂ + 3 g₁² t₁ - g₁ t₂)²`, `q₂` tied at `H`.  On the face it
equals `κ₇ H²`. -/
def alignedEighthNonsquarePeeledRow610 {K : Type*} [CommRing K]
    (H g1 t1 t2 a0 a1 a2 b2 : K[X]) (κ κ₃ κ₅ : K) : K[X] :=
  (1280 : K[X]) *
      ((81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2) ^ 2 +
    H * ((2799360 : K[X]) * g1 ^ 2 * a0 -
      (38400 : K[X]) * g1 ^ 2 * t1 ^ 3 +
      (15360 : K[X]) * g1 * t1 ^ 2 * t2 -
      (1866240 : K[X]) * g1 * a1 * t1 + (622080 : K[X]) * a1 * t2 -
      (311040 : K[X]) * a2 * t1 ^ 2 - (1280 : K[X]) * t1 * t2 ^ 2 -
      (15116544 : K[X]) * b2 +
      Polynomial.C κ * ((13824 : K[X]) * g1 ^ 2 * t1 ^ 2 -
        (6144 : K[X]) * g1 * t1 * t2 + (512 : K[X]) * t2 ^ 2 +
        (746496 : K[X]) * g1 * a1 + (248832 : K[X]) * a2 * t1) -
      Polynomial.C κ₃ * ((31104 : K[X]) * a2) -
      Polynomial.C κ₅ * ((16 : K[X]) * g1 ^ 2)) +
    H ^ 2 * ((5598720 : K[X]) * a0 * t1 + (3840 : K[X]) * t1 ^ 4 +
      Polynomial.C κ * ((2239488 : K[X]) * a0 - (3072 : K[X]) * t1 ^ 3) -
      Polynomial.C κ₅ * ((32 : K[X]) * t1))

/-- Solved block of the nonsquare eighth row after the `u`-substitution
peels the last `H`: `15116544 q₂` equals this block minus `κ₇ H`. -/
def alignedEighthNonsquareSolved610 {K : Type*} [CommRing K]
    (H g1 t1 t2 u a0 a1 : K[X]) (κ κ₃ κ₅ : K) : K[X] :=
  (2799360 : K[X]) * g1 ^ 2 * a0 - (26880 : K[X]) * g1 ^ 2 * t1 ^ 3 -
    (1866240 : K[X]) * g1 * a1 * t1 +
    (11520 : K[X]) * g1 * t1 ^ 2 * t2 + (622080 : K[X]) * a1 * t2 -
    (1280 : K[X]) * t1 * t2 ^ 2 +
    Polynomial.C κ * ((4608 : K[X]) * g1 ^ 2 * t1 ^ 2 -
      (3072 : K[X]) * g1 * t1 * t2 + (512 : K[X]) * t2 ^ 2 +
      (746496 : K[X]) * g1 * a1) +
    Polynomial.C κ₃ * ((1152 : K[X]) * g1 ^ 2 * t1 -
      (384 : K[X]) * g1 * t2) -
    Polynomial.C κ₅ * ((16 : K[X]) * g1 ^ 2) +
    H * ((5598720 : K[X]) * a0 * t1 + (3840 : K[X]) * t1 ^ 4 -
      (3840 : K[X]) * t1 ^ 2 * u + (1280 : K[X]) * u ^ 2 +
      Polynomial.C κ * ((2239488 : K[X]) * a0 - (3072 : K[X]) * t1 ^ 3 +
        (3072 : K[X]) * t1 * u) -
      Polynomial.C κ₃ * ((384 : K[X]) * u) -
      Polynomial.C κ₅ * ((32 : K[X]) * t1))

set_option maxHeartbeats 3200000000 in
/-- Descent of the consumed degree-`7` row in the nonsquare chamber:
the `H¹⁶`-peeled core absorbs the octic head through the seventh-face
divisibilities, cancelling `H²` more leaves the peeled row with
PERFECT-SQUARE head `1280 (81 p₂ + 3 g₁² t₁ - g₁ t₂)²`, which vanishes
at BOTH simple roots and transfers to the NEW divisibility
`81 p₂ + 3 g₁² t₁ - g₁ t₂ = H u` — the first constraint on `p₂` in the
aligned tower — and substituting `u` cancels one more `H`, solving `q₂`
OUTRIGHT. -/
theorem alignedNonsquareEighth_descent_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H g1 f t1 t2 a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 : k[X]}
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
    (ht1 : (3 : k[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : k[X]) * a3 - g1 ^ 3 = H * t2) :
    ∃ u : k[X],
      (81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 - g1 * t2 = H * u ∧
      alignedEighthNonsquarePeeledRow610 H g1 t1 t2 a0 a1 a2 b2
          κ κ₃ κ₅ = Polynomial.C κ₇ * H ^ 2 ∧
      (15116544 : k[X]) * b2 =
        alignedEighthNonsquareSolved610 H g1 t1 t2 u a0 a1 κ κ₃ κ₅ -
          Polynomial.C κ₇ * H := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hcore :
      (311040 : k[X]) * f ^ 4 - (1451520 : k[X]) * f ^ 3 * g1 ^ 2 +
          (1209600 : k[X]) * f ^ 2 * g1 ^ 4 +
          (3732480 : k[X]) * f ^ 2 * g1 * a3 -
          (349440 : k[X]) * f * g1 ^ 6 -
          (2903040 : k[X]) * f * g1 ^ 3 * a3 -
          (2799360 : k[X]) * f * a3 ^ 2 + (33280 : k[X]) * g1 ^ 8 +
          (483840 : k[X]) * g1 ^ 5 * a3 +
          (1866240 : k[X]) * g1 ^ 2 * a3 ^ 2 +
          H * (Polynomial.C κ * ((373248 : k[X]) * a3 ^ 2 +
              (138240 : k[X]) * g1 ^ 3 * a3 + (11264 : k[X]) * g1 ^ 6 -
              (82944 : k[X]) * f ^ 3 +
              (207360 : k[X]) * f ^ 2 * g1 ^ 2 -
              (497664 : k[X]) * f * g1 * a3 -
              (92160 : k[X]) * f * g1 ^ 4) -
            (2799360 : k[X]) * f ^ 2 * a2 +
            (3732480 : k[X]) * f * g1 ^ 2 * a2 -
            (725760 : k[X]) * g1 ^ 4 * a2 -
            (5598720 : k[X]) * g1 * a2 * a3) +
          H ^ 2 * (Polynomial.C κ * ((746496 : k[X]) * f * a2 -
              (248832 : k[X]) * g1 ^ 2 * a2) -
            (5598720 : k[X]) * f * g1 * a1 +
            (1244160 : k[X]) * g1 ^ 3 * a1 +
            (16796160 : k[X]) * a1 * a3 + (8398080 : k[X]) * a2 ^ 2) +
          H ^ 3 * ((16796160 : k[X]) * f * a0 -
            (2799360 : k[X]) * g1 ^ 2 * a0 - (15116544 : k[X]) * b2 +
            Polynomial.C κ * ((746496 : k[X]) * g1 * a1) -
            Polynomial.C κ₃ * ((31104 : k[X]) * a2) -
            Polynomial.C κ₅ * ((96 : k[X]) * f - (16 : k[X]) * g1 ^ 2)) +
          H ^ 4 * (Polynomial.C κ * ((2239488 : k[X]) * a0)) =
        Polynomial.C κ₇ * H ^ 4 := by
    have hJ' := hJ
    simp only [alignedEighthDefect610] at hJ'
    rw [hD0, hE, hF0, hG, hI0, hg1, hf] at hJ'
    apply mul_left_cancel₀ (pow_ne_zero 16 hH)
    linear_combination hJ'
  have hR8 :
      (1280 : k[X]) *
          ((81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 - g1 * t2) ^ 2 +
          H * ((2799360 : k[X]) * g1 ^ 2 * a0 -
            (38400 : k[X]) * g1 ^ 2 * t1 ^ 3 +
            (15360 : k[X]) * g1 * t1 ^ 2 * t2 -
            (1866240 : k[X]) * g1 * a1 * t1 +
            (622080 : k[X]) * a1 * t2 -
            (311040 : k[X]) * a2 * t1 ^ 2 -
            (1280 : k[X]) * t1 * t2 ^ 2 - (15116544 : k[X]) * b2 +
            Polynomial.C κ * ((13824 : k[X]) * g1 ^ 2 * t1 ^ 2 -
              (6144 : k[X]) * g1 * t1 * t2 + (512 : k[X]) * t2 ^ 2 +
              (746496 : k[X]) * g1 * a1 + (248832 : k[X]) * a2 * t1) -
            Polynomial.C κ₃ * ((31104 : k[X]) * a2) -
            Polynomial.C κ₅ * ((16 : k[X]) * g1 ^ 2)) +
          H ^ 2 * ((5598720 : k[X]) * a0 * t1 + (3840 : k[X]) * t1 ^ 4 +
            Polynomial.C κ * ((2239488 : k[X]) * a0 -
              (3072 : k[X]) * t1 ^ 3) -
            Polynomial.C κ₅ * ((32 : k[X]) * t1)) =
        Polynomial.C κ₇ * H ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore +
      (-((138240 : k[X]) * f ^ 2 * g1) + (111360 : k[X]) * f * g1 ^ 3 +
        (103680 : k[X]) * f * a3 - (20480 : k[X]) * g1 ^ 5 -
        (69120 : k[X]) * g1 ^ 2 * a3 + (3840 : k[X]) * H * f * t2 -
        (2560 : k[X]) * H * g1 ^ 2 * t2 +
        (207360 : k[X]) * H * g1 * a2 - (622080 : k[X]) * H ^ 2 * a1 +
        Polynomial.C κ * ((18432 : k[X]) * H * f * g1 -
          (5632 : k[X]) * H * g1 ^ 3 - (13824 : k[X]) * H * a3 -
          (512 : k[X]) * H ^ 2 * t2)) * ht2 +
      (-((103680 : k[X]) * f ^ 3) + (449280 : k[X]) * f ^ 2 * g1 ^ 2 -
        (299520 : k[X]) * f * g1 ^ 4 + (53760 : k[X]) * g1 ^ 6 -
        (34560 : k[X]) * H * f ^ 2 * t1 +
        (138240 : k[X]) * H * f * g1 ^ 2 * t1 -
        (46080 : k[X]) * H * f * g1 * t2 +
        (933120 : k[X]) * H * f * a2 -
        (53760 : k[X]) * H * g1 ^ 4 * t1 +
        (23040 : k[X]) * H * g1 ^ 3 * t2 -
        (933120 : k[X]) * H * g1 ^ 2 * a2 -
        (11520 : k[X]) * H ^ 2 * f * t1 ^ 2 +
        (42240 : k[X]) * H ^ 2 * g1 ^ 2 * t1 ^ 2 +
        (1866240 : k[X]) * H ^ 2 * g1 * a1 -
        (15360 : k[X]) * H ^ 2 * g1 * t1 * t2 +
        (311040 : k[X]) * H ^ 2 * a2 * t1 +
        (1280 : k[X]) * H ^ 2 * t2 ^ 2 -
        (5598720 : k[X]) * H ^ 3 * a0 -
        (3840 : k[X]) * H ^ 3 * t1 ^ 3 +
        Polynomial.C κ * ((27648 : k[X]) * H * f ^ 2 -
          (59904 : k[X]) * H * f * g1 ^ 2 +
          (16896 : k[X]) * H * g1 ^ 4 +
          (9216 : k[X]) * H ^ 2 * f * t1 -
          (16896 : k[X]) * H ^ 2 * g1 ^ 2 * t1 +
          (6144 : k[X]) * H ^ 2 * g1 * t2 -
          (248832 : k[X]) * H ^ 2 * a2 +
          (3072 : k[X]) * H ^ 3 * t1 ^ 2) +
        Polynomial.C κ₅ * ((32 : k[X]) * H ^ 3)) * ht1
  have hkey : ∀ a : k, H.eval a = 0 →
      ((81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 - g1 * t2).eval a =
        0 := by
    intro a ha
    have hev := congrArg (fun t : k[X] => t.eval a) hR8
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat] at hev
    rw [ha] at hev
    have hsq :
        (((81 : k[X]) * a2 + (3 : k[X]) * g1 ^ 2 * t1 -
          g1 * t2).eval a) ^ 2 = 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat]
      linear_combination ((1280 : k)⁻¹) * hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  obtain ⟨u, hu⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hkey
  have hq2 :
      (15116544 : k[X]) * b2 =
        ((2799360 : k[X]) * g1 ^ 2 * a0 -
          (26880 : k[X]) * g1 ^ 2 * t1 ^ 3 -
          (1866240 : k[X]) * g1 * a1 * t1 +
          (11520 : k[X]) * g1 * t1 ^ 2 * t2 +
          (622080 : k[X]) * a1 * t2 - (1280 : k[X]) * t1 * t2 ^ 2 +
          Polynomial.C κ * ((4608 : k[X]) * g1 ^ 2 * t1 ^ 2 -
            (3072 : k[X]) * g1 * t1 * t2 + (512 : k[X]) * t2 ^ 2 +
            (746496 : k[X]) * g1 * a1) +
          Polynomial.C κ₃ * ((1152 : k[X]) * g1 ^ 2 * t1 -
            (384 : k[X]) * g1 * t2) -
          Polynomial.C κ₅ * ((16 : k[X]) * g1 ^ 2) +
          H * ((5598720 : k[X]) * a0 * t1 + (3840 : k[X]) * t1 ^ 4 -
            (3840 : k[X]) * t1 ^ 2 * u + (1280 : k[X]) * u ^ 2 +
            Polynomial.C κ * ((2239488 : k[X]) * a0 -
              (3072 : k[X]) * t1 ^ 3 + (3072 : k[X]) * t1 * u) -
            Polynomial.C κ₃ * ((384 : k[X]) * u) -
            Polynomial.C κ₅ * ((32 : k[X]) * t1))) -
          Polynomial.C κ₇ * H := by
    apply mul_left_cancel₀ hH
    linear_combination -hR8 -
      (Polynomial.C κ₃ * ((384 : k[X]) * H) -
        Polynomial.C κ * ((3072 : k[X]) * H * t1) +
        (3840 : k[X]) * H * t1 ^ 2 - (1280 : k[X]) * H * u -
        (3840 : k[X]) * g1 ^ 2 * t1 + (1280 : k[X]) * g1 * t2 -
        (103680 : k[X]) * a2) * hu
  refine ⟨u, hu, ?_, ?_⟩
  · simp only [alignedEighthNonsquarePeeledRow610]
    linear_combination hR8
  · simp only [alignedEighthNonsquareSolved610]
    linear_combination hq2

/-! ## Source-facing eighth-row packets -/

/-- Source-facing weight-twenty integral of a normalized aligned
scale-two `(6,10)` source: the degree-`7` row is consumed into
`J = κ₇ H²⁰` on top of the previous aligned packet.  The even exponent
is chamber-free. -/
theorem normalized610ScaleTwo_alignedEighthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ : K),
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
          Polynomial.C κ₇ * H ^ 20 := by
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
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, aligned_q9_solved_610 haligned, hM,
    hD2, hE, hF2, hG, hI2, hJ⟩

/-- Exact square-chamber eighth packet of a normalized aligned
scale-two `(6,10)` source: the chamber-free `J = κ₇ H²⁰`, the twice
`h₀`-peeled row with head `1280 w₁² (e₂ - 3 e₁ w₁)²` and `q₂` tied at
`h₀⁴`, the NEW product divisibility `w₁ (e₂ - 3 e₁ w₁) = h₀ u₂`, and
the combined row (eighth plus `2 w₁` times the seventh) with head
`-1280 e₁ (3 e₁ w₁ - e₂)(6 e₁ w₁ - e₂) - 189 μ w₁⁵`. -/
theorem normalized610ScaleTwo_alignedEighthFace_squareChamber_packet
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
    ∃ (κ μ κ₃ ν κ₅ ν₂ κ₇ : K) (w1 f2 e1 e2 u2 : K[X]),
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
          Polynomial.C κ₇ * H ^ 20 := by
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
  obtain ⟨r, htie4, hq6⟩ := alignedSquareFourth_tie_610 hcore4
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨ν, _hν2, hF⟩ := alignedSquareFifth_sqrt_610 hh0 hHsq hF2
  have hcore5 := alignedSquareFifth_core_610 hh0 hHsq hp5 hD hE4 hF
  obtain ⟨w1, f1, hw1, hf1, hq5⟩ :=
    alignedSquareFifth_descent_610 hh0 hdeg1 hcore5 htie4
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hp5w1 : p.coeff 5 = h0 ^ 4 * w1 := by rw [hp5, hw1]; ring
  have hcore6 := alignedSquareSixth_core_610 hh0 hHsq hp5w1 hf1 hD hE4
    hF hG
  obtain ⟨f2, hf2, hcore2⟩ :=
    alignedSquareSixth_descent_610 hh0 hdeg1 hcore6
  obtain ⟨s, htie6, _hq4⟩ := alignedSquareSixth_tie_610 hcore2
  have hp4f2 : p.coeff 4 = h0 ^ 2 * f2 := by rw [hf1, hf2]; ring
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨ν₂, _hν₂2, hI⟩ := alignedSquareSeventh_sqrt_610 hh0 hHsq hI2
  obtain ⟨e1, e2, he1, he2, _hsref, hR⟩ :=
    alignedSquareSeventh_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hE4
      hF hG hI htie6
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨u2, hu2, hR8, hQ9⟩ :=
    alignedSquareEighth_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hE4
      hF hG hI hJ he1 he2 hR
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, w1, f2, e1, e2, u2, hM, hp5w1, hp4f2,
    he1, he2, hu2, hR8, hQ9, hD, hE4, hF, hG, hI, hJ⟩

/-- Exact nonsquare-chamber eighth packet of a normalized aligned
scale-two `(6,10)` source: the chamber-free `J = κ₇ H²⁰`, the twice
`H`-peeled row with PERFECT-SQUARE head
`1280 (81 p₂ + 3 g₁² t₁ - g₁ t₂)²`, the NEW divisibility
`81 p₂ + 3 g₁² t₁ - g₁ t₂ = H u` (the first constraint on `p₂` in the
aligned tower), and `q₂` solved OUTRIGHT. -/
theorem normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
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
    ∃ (κ κ₃ κ₅ κ₇ : K) (g1 f t1 t2 u : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        alignedEighthNonsquarePeeledRow610 H g1 t1 t2 (p.coeff 0)
            (p.coeff 1) (p.coeff 2) (q.coeff 2) κ κ₃ κ₅ =
          Polynomial.C κ₇ * H ^ 2 ∧
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
          Polynomial.C κ₇ * H ^ 20 := by
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
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk4, hF0⟩ :=
    alignedNonsquareFifth_defect_eq_zero_610 hH hHdegree hnsq hF2
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  have hcore6 := alignedNonsquareSixth_core_610 hH hp5 hf hD0 hE4 hF0 hG
  obtain ⟨t, ht⟩ := alignedNonsquareSixth_dvd_610 hHdegree hnsq hcore6
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hk6, hI0⟩ :=
    alignedNonsquareSeventh_defect_eq_zero_610 hH hHdegree hnsq hI2
  obtain ⟨t1, t2, ht1, ht2, _htref, _hq3⟩ :=
    alignedNonsquareSeventh_solved_610 hH hHdegree hnsq hp5 hf hD0 hE4
      hF0 hG hI0 ht
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨u, hu, hR8, hq2⟩ :=
    alignedNonsquareEighth_descent_610 hH hHdegree hnsq hp5 hf hD0 hE4
      hF0 hG hI0 hJ ht1 ht2
  exact ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, hM, hp5, hf, ht1, ht2, hu,
    hR8, hq2, hD0, hE4, hF0, hG, hI0, hJ⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`7`
aligned row (peeled rows, solved `q₂`, and factored defect relations
are in the two chamber packets above).  Neither chamber is excluded
and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedEighthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (w1 f2 e1 e2 u2 : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t1 t2 u : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedEighthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, w1, f2, e1, e2, u2, _hM, hp5, hp4,
      he1, he2, hu2, _hR8, _hQ9, _hD, _hE, _hF, _hG, _hI, _hJ⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, w1, f2, e1, e2, u2, hp5, hp4, he1,
      he2, hu2⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, g1, f, t1, t2, u, _hM, hp5, hf, ht1, ht2, hu,
      _hR8, _hq2, _hD0, _hE, _hF0, _hG, _hI0, _hJ⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t1, t2, u, hp5, hf, ht1, ht2, hu⟩

/-- Root data of the consumed degree-`7` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇, p₄, q₆` vanishes and the
seventh-face pins hold; in the square chamber the combined row REFINES
the seventh-face residual branch to
`(w₁(a) = 0 ∧ (e₁(a) = 0 ∨ e₂(a) = 0)) ∨`
`(e₂(a) = 3 e₁(a) w₁(a) ∧ (μ = 0 ∨ w₁(a) = 0))`, and in the nonsquare
chamber the perfect-square head pins
`81 p₂(a) = g₁(a) t₂(a) - 3 g₁(a)² t₁(a)` — the first root constraint
on `p₂` in the aligned tower. -/
theorem normalized610ScaleTwo_alignedEighthFace_rootData
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
      ((∃ h0 w1 f2 e1 e2 : K[X], ∃ κ μ : K, h0 ≠ 0 ∧ H = h0 ^ 2 ∧
          h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
            Polynomial.C κ * H ^ 5 ∧
          alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
          3 * f2.eval a = w1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = w1.eval a ^ 3 ∧
          ((w1.eval a = 0 ∧ (e1.eval a = 0 ∨ e2.eval a = 0)) ∨
            (e2.eval a = 3 * e1.eval a * w1.eval a ∧
              (μ = 0 ∨ w1.eval a = 0)))) ∨
        (∃ g1 f t1 t2 u : K[X], p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          3 * f.eval a = g1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = g1.eval a ^ 3 ∧
          81 * (p.coeff 2).eval a =
            g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a)) := by
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
    have hpacket8 :=
      normalized610ScaleTwo_alignedEighthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket8
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, ν₂B, κ₇B, w1, f2, e1, e2, u2, hM8,
      hp5w1, hp4f2, he1, he2, _hu2, hR8, hQ9, hD8, _hE, _hF, _hG, _hI,
      _hJ⟩ := hpacket8
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
    have hevR8 := congrArg (fun t : K[X] => t.eval a) hR8
    simp only [alignedEighthSquarePeeledRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevR8
    rw [hroot] at hevR8
    have h1sq :
        (w1.eval a * (e2.eval a - 3 * e1.eval a * w1.eval a)) ^ 2 =
          0 := by
      linear_combination ((1280 : K)⁻¹) * hevR8
    have h1 : w1.eval a * (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1sq
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
    have hres := alignedEighthCombinedResolve_610 h1 h2
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, e1, e2, κB, μB, hh0, hHsq, hroot, hp5w1,
        hp4f2, he1, he2, hM8, hD8, hpin1, hpin2, hres⟩⟩
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
    have hpacket8 :=
      normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket8
    obtain ⟨κB, κ₃B, κ₅B, κ₇B, g1, f, t1, t2, u, _hM8, hp5, hf, ht1,
      ht2, hu, _hR8, _hq2, _hD0, _hE, _hF0, _hG, _hI0, _hJ⟩ := hpacket8
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
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, t1, t2, u, hp5, hf, ht1, ht2, hu, hpin1, hpin2,
        hp2pin⟩⟩
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

#print axioms alignedEighthCoefficientJacobianRow_610
#print axioms alignedEighthDefect_weightedDerivative_identity_610
#print axioms alignedEighthDefectRow_eq_zero_610
#print axioms alignedEighthDefectPowerRelation_610
#print axioms alignedSquareEighth_descent_610
#print axioms alignedEighthCombinedResolve_610
#print axioms alignedNonsquareEighth_descent_610
#print axioms normalized610ScaleTwo_alignedEighthFace_packet
#print axioms normalized610ScaleTwo_alignedEighthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedEighthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedEighthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedEighthFace_rootData

end Max11DegreeRoutes
