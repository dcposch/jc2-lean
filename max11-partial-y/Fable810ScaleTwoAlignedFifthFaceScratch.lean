import Fable810ScaleTwoAlignedFourthFaceScratch

/-! # Fifth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedFourthFaceScratch` consumed the degree-`12`
aligned Keller row of the normalized scale-two `(8,10)` source: the
squared weight-thirty-five integral `F² = κ₄ H³⁵`, its chamber split,
the cleared fifth rows, and the absorbed root quintic.  This file
consumes the next unused aligned row, the degree-`11` Jacobian
coefficient — the first row that sees `p₂` and `q₄` (internal names
`alignedSixth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation
`C = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇² - κ H⁷ = 0`, and the consumed
degree-`14`/`13`/`12` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, the degree-`11` row is
the weighted derivative of the weight-forty-two defect

`G = 81920 p₂ H²⁰ - 65536 q₄ H¹⁹ - 30720 p₃ p₇ H¹⁶ + 40960 q₅ p₇ H¹⁵
  - 40960 p₄ p₆ H¹⁶ + 49152 q₆ p₆ H¹⁵ + 25600 p₄ p₇² H¹²
  - 36864 q₆ p₇² H¹¹ - 61440 p₅² H¹⁶ + 57344 p₅ q₇ H¹⁵
  + 46080 p₅ p₆ p₇ H¹² - 86016 q₇ p₆ p₇ H¹¹ - 21760 p₅ p₇³ H⁸
  + 35840 q₇ p₇³ H⁷ - 10240 p₆³ H¹² + 49920 p₆² p₇² H⁸
  - 25600 p₆ p₇⁴ H⁴ + 2800 p₇⁶
  + κ (2048 p₄ H¹⁹ - 3072 p₅ p₇ H¹⁵ - 1536 p₆² H¹⁵ + 3840 p₆ p₇² H¹¹
       - 1120 p₇⁴ H⁷)`,

via the exact multiplier identity

`8192 H¹² H⁴ · row₁₁[p₈ = H⁴, q₁₀ = H⁵] = (H G' - 21 G H')
  - 18432 H¹⁶ p₃' N + 6144 H¹⁶ p₃ N'
  + (2048 H¹³ p₄' + 3072 p₄ H¹² H') C - 1024 H¹³ p₄ C'
  + (384 p₅ H⁸ + 336 p₆ p₇ H⁴ - 7 p₇³) (2 H D' - 21 D H')
  + (48 p₆ H⁴ + 18 p₇²) (H E' - 14 E H') + 3 p₇ (2 H F' - 35 F H')`.

On the aligned face every right-hand correction vanishes, so
`H G' = 21 G H'` and the weight-forty-two first integral

`G = κ₅ H²¹`

holds for a preserved constant `κ₅`.  The exponent `42 = 2·21` is
even, so — exactly as for the degree-`13` row — the integral is
**chamber-free**: no square root and no forced vanishing of `κ₅` in
either chamber.

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: peeling `h₀²⁴` and
  consuming the previous factored quotient (`128 q₇ h₀²` solved,
  transported by the mate `56 (8 p₅ h₀⁴ - 12 p₆ g₁ + 5 g₁³)`) leaves
  the cleared sixth row
  `81920 p₂ h₀¹⁶ - 65536 q₄ h₀¹⁴ - 30720 p₃ g₁ h₀¹² + 40960 q₅ g₁ h₀¹⁰
   - 40960 p₄ p₆ h₀⁸ + 25600 p₄ g₁² h₀⁸ + 10240 p₅² h₀⁸
   + 49152 q₆ p₆ h₀⁶ - 36864 q₆ g₁² h₀⁶ - 43520 p₅ p₆ g₁ h₀⁴
   + 20800 p₅ g₁³ h₀⁴ - 10240 p₆³ + 23040 p₆² g₁² - 11040 p₆ g₁⁴
   + 1400 g₁⁶ + κ (2048 p₄ h₀¹⁴ - 1280 p₅ g₁ h₀¹⁰ - 1536 p₆² h₀⁶
   + 1152 p₆ g₁² h₀⁶) - μ (448 p₅ h₀¹³ - 672 p₆ g₁ h₀⁹
   + 280 g₁³ h₀⁹) = κ₅ h₀¹⁸`
  with the factored transport form
  `40 (35 g₁⁶ - 276 p₆ g₁⁴ + 576 p₆² g₁² - 256 p₆³) = h₀² · (co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): `κ₅`
  is **not** forced to vanish.  With `p₇ = H² g₂`, peeling `H¹²` and
  consuming the previous factored quotient (same mate) leaves the
  cleared sixth row with `κ₅ H⁹` on the right and the transport
  `40 (35 g₂⁶ - 276 p₆ g₂⁴ + 576 p₆² g₂² - 256 p₆³) = H · (co-factor)`.

At a root of the core the transport leaves the honest root sextic
`35 g⁶ - 276 p₆ g⁴ + 576 p₆² g² - 256 p₆³ = 0`.  Like the quintic of
the previous row it adds *no new* root information: the consumed
degree-`13` row already collapsed `g(a) = 0 ∧ p₆(a) = 0` at every core
root, and that collapse absorbs the sextic identically
(`alignedSixth_rootSextic_absorbed_810`).  The chamber-independent
root jet therefore stays `p₇, q₉, q₈, p₆` — the row ties the new
coefficients `p₂, q₄` into the cleared sixth row (at `h₀¹⁶`/`h₀¹⁴`,
resp. `H⁸`/`H⁷`) instead of killing anything new at the root.

No closure is claimed.  Both chambers remain open, the constants `κ`,
`μ`, `κ₃`, `κ₄`, `κ₅` are preserved where not previously forced, the
zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`,
`κ₄ = 0`, `κ₅ = 0`) are not excluded as polynomial identities, the
deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H` from the
degree-`13` face are still not re-cleared through the tower here, the
root sextic is recorded but not excluded as an identity, and no
individual vanishing of `p₂`, `p₃`, `p₄`, `p₅`, `q₄`, `q₅`, `q₆`,
`q₇` is claimed.  The next unused Keller row on the aligned face is
the degree-`10` Jacobian coefficient, the first row that sees `p₁` and
`q₃` (weight-forty-nine defect, odd exponent, hence chambered).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`11` Keller coefficient on the aligned face -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`11` Jacobian coefficient, the first
aligned row that sees `p₂` and `q₄`. -/
theorem alignedSixthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 7).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 4).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 5).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) *
          (q.coeff 10).derivative) = 0 := by
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
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned sixth defect -/

/-- Weight-forty-two defect of the degree-`11` aligned `(8,10)` row.
On the aligned face it is a polynomial first integral of even weight
forty-two, hence chamber-free. -/
def alignedSixthDefect810 {K : Type*} [CommRing K]
    (H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (81920 : K[X]) * a2 * H ^ 20 - (65536 : K[X]) * b4 * H ^ 19 -
    (30720 : K[X]) * a3 * a7 * H ^ 16 +
    (40960 : K[X]) * b5 * a7 * H ^ 15 -
    (40960 : K[X]) * a4 * a6 * H ^ 16 +
    (49152 : K[X]) * b6 * a6 * H ^ 15 +
    (25600 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
    (36864 : K[X]) * b6 * a7 ^ 2 * H ^ 11 -
    (61440 : K[X]) * a5 ^ 2 * H ^ 16 +
    (57344 : K[X]) * a5 * b7 * H ^ 15 +
    (46080 : K[X]) * a5 * a6 * a7 * H ^ 12 -
    (86016 : K[X]) * b7 * a6 * a7 * H ^ 11 -
    (21760 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
    (35840 : K[X]) * b7 * a7 ^ 3 * H ^ 7 -
    (10240 : K[X]) * a6 ^ 3 * H ^ 12 +
    (49920 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
    (25600 : K[X]) * a6 * a7 ^ 4 * H ^ 4 + (2800 : K[X]) * a7 ^ 6 +
    Polynomial.C κ *
      ((2048 : K[X]) * a4 * H ^ 19 - (3072 : K[X]) * a5 * a7 * H ^ 15 -
        (1536 : K[X]) * a6 ^ 2 * H ^ 15 +
        (3840 : K[X]) * a6 * a7 ^ 2 * H ^ 11 -
        (1120 : K[X]) * a7 ^ 4 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`11` Jacobian expression with the
weighted derivative of `G`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, and degree-`12` rows. -/
theorem alignedSixthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (8192 : K[X]) * H ^ 16 *
        ((H ^ 4).derivative * (b4 * (4 : K[X])) +
          a7.derivative * (b5 * (5 : K[X])) +
          a6.derivative * (b6 * (6 : K[X])) +
          a5.derivative * (b7 * (7 : K[X])) +
          a4.derivative * (b8 * (8 : K[X])) +
          a3.derivative * (b9 * (9 : K[X])) +
          a2.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b4.derivative +
          (a7 * (7 : K[X])) * b5.derivative +
          (a6 * (6 : K[X])) * b6.derivative +
          (a5 * (5 : K[X])) * b7.derivative +
          (a4 * (4 : K[X])) * b8.derivative +
          (a3 * (3 : K[X])) * b9.derivative +
          (a2 * (2 : K[X])) * (H ^ 5).derivative)) =
      (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
            κ).derivative -
        (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6
          b7 κ * H.derivative) -
        (18432 : K[X]) * H ^ 16 * a3.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (6144 : K[X]) * H ^ 16 * a3 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((2048 : K[X]) * H ^ 13 * a4.derivative +
            (3072 : K[X]) * a4 * H ^ 12 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (1024 : K[X]) * H ^ 13 * a4 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((384 : K[X]) * a5 * H ^ 8 + (336 : K[X]) * a6 * a7 * H ^ 4 -
            (7 : K[X]) * a7 ^ 3) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((48 : K[X]) * a6 * H ^ 4 + (18 : K[X]) * a7 ^ 2) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        (3 : K[X]) * a7 *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) := by
  simp only [alignedSixthDefect810, alignedFifthDefect810,
    alignedFourthDefect810, alignedThirdDefect810,
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

/-- On the aligned face, with the consumed degree-`15`, degree-`14`,
degree-`13`, and degree-`12` rows, the degree-`11` row is the weighted
derivative `H G' - 21 G H' = 0`. -/
theorem alignedSixthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    H * (alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ).derivative -
      (21 : K[X]) *
        alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedSixthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC3, hC2] at hrow
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
  have hrowE :
      H * (alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ).derivative -
        (14 : K[X]) *
          alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedFourthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowF :
      (2 : K[X]) * H *
          (alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (35 : K[X]) *
          alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedFifthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hid := alignedSixthDefect_weightedDerivative_identity_810
    H (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
    (p.coeff 7) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
    (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD, hrowE, hrowF] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Weight-forty-two polynomial first integral of the aligned `(8,10)`
sixth defect: `G = κ₅ H²¹`.  The exponent is even, so the integral is
chamber-free. -/
theorem alignedSixthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₅ : K,
      alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
          (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
          (q.coeff 6) (q.coeff 7) κ =
        Polynomial.C κ₅ * H ^ 21 := by
  let G : K[X] :=
    alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
      (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ
  have hrow : H * G.derivative - (21 : K[X]) * G * H.derivative = 0 := by
    simpa only [G] using
      alignedSixthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC21 : Polynomial.C (21 : K) = (21 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian G (H ^ 21) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      G * (Polynomial.C (21 : K) * H ^ (21 - 1) * H.derivative) -
          G.derivative * H ^ 21 =
          H ^ 20 *
            (Polynomial.C (21 : K) * G * H.derivative -
              H * G.derivative) := by ring
      _ = 0 := by
        rw [hC21]
        have hfac :
            (21 : K[X]) * G * H.derivative - H * G.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 21 hH) hW

/-! ## Root sextic of the factored transport and its absorption -/

/-- Evaluating a factored-transport sixth row at a root of its
cofactor: the root sextic `35 g⁶ - 276 p₆ g⁴ + 576 p₆² g² - 256 p₆³`
vanishes there.  The sextic is not excluded as an identity. -/
theorem alignedSixth_factored_rootSextic_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (40 : K[X]) *
        ((35 : K[X]) * g ^ 6 - (276 : K[X]) * a6 * g ^ 4 +
          (576 : K[X]) * a6 ^ 2 * g ^ 2 - (256 : K[X]) * a6 ^ 3) = W)
    {a : K} (hW : W.eval a = 0) :
    35 * (g.eval a) ^ 6 - 276 * a6.eval a * (g.eval a) ^ 4 +
      576 * (a6.eval a) ^ 2 * (g.eval a) ^ 2 -
      256 * (a6.eval a) ^ 3 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  have hs := (mul_eq_zero.mp hev).resolve_left
    (by norm_num : (40 : K) ≠ 0)
  linear_combination hs

/-- The root sextic of the consumed degree-`11` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the sixth row adds no new root
constraint. -/
theorem alignedSixth_rootSextic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    35 * G ^ 6 - 276 * P6 * G ^ 4 + 576 * P6 ^ 2 * G ^ 2 -
      256 * P6 ^ 3 = 0 := by
  rw [hG, hP6]
  ring

/-! ## Square chamber -/

/-- Peeling `h₀²⁴` from `G = κ₅ h₀⁴²` on `p₇ = h₀⁴ g₁` leaves the
square-chamber sixth core. -/
theorem alignedSquareSixth_core_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 : K[X]} {κ κ₅ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hG : alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 21) :
    (81920 : K[X]) * a2 * h0 ^ 16 - (65536 : K[X]) * b4 * h0 ^ 14 -
        (30720 : K[X]) * a3 * g1 * h0 ^ 12 +
        (40960 : K[X]) * b5 * g1 * h0 ^ 10 -
        (40960 : K[X]) * a4 * a6 * h0 ^ 8 +
        (49152 : K[X]) * b6 * a6 * h0 ^ 6 +
        (25600 : K[X]) * a4 * g1 ^ 2 * h0 ^ 8 -
        (36864 : K[X]) * b6 * g1 ^ 2 * h0 ^ 6 -
        (61440 : K[X]) * a5 ^ 2 * h0 ^ 8 +
        (57344 : K[X]) * a5 * b7 * h0 ^ 6 +
        (46080 : K[X]) * a5 * a6 * g1 * h0 ^ 4 -
        (86016 : K[X]) * b7 * a6 * g1 * h0 ^ 2 -
        (21760 : K[X]) * a5 * g1 ^ 3 * h0 ^ 4 +
        (35840 : K[X]) * b7 * g1 ^ 3 * h0 ^ 2 -
        (10240 : K[X]) * a6 ^ 3 + (49920 : K[X]) * a6 ^ 2 * g1 ^ 2 -
        (25600 : K[X]) * a6 * g1 ^ 4 + (2800 : K[X]) * g1 ^ 6 +
        Polynomial.C κ *
          ((2048 : K[X]) * a4 * h0 ^ 14 -
            (3072 : K[X]) * a5 * g1 * h0 ^ 10 -
            (1536 : K[X]) * a6 ^ 2 * h0 ^ 6 +
            (3840 : K[X]) * a6 * g1 ^ 2 * h0 ^ 6 -
            (1120 : K[X]) * g1 ^ 4 * h0 ^ 6) =
      Polynomial.C κ₅ * h0 ^ 18 := by
  have hG' :
      (81920 : K[X]) * a2 * (h0 ^ 2) ^ 20 -
          (65536 : K[X]) * b4 * (h0 ^ 2) ^ 19 -
          (30720 : K[X]) * a3 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 16 +
          (40960 : K[X]) * b5 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 15 -
          (40960 : K[X]) * a4 * a6 * (h0 ^ 2) ^ 16 +
          (49152 : K[X]) * b6 * a6 * (h0 ^ 2) ^ 15 +
          (25600 : K[X]) * a4 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 12 -
          (36864 : K[X]) * b6 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 11 -
          (61440 : K[X]) * a5 ^ 2 * (h0 ^ 2) ^ 16 +
          (57344 : K[X]) * a5 * b7 * (h0 ^ 2) ^ 15 +
          (46080 : K[X]) * a5 * a6 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 12 -
          (86016 : K[X]) * b7 * a6 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 11 -
          (21760 : K[X]) * a5 * (h0 ^ 4 * g1) ^ 3 * (h0 ^ 2) ^ 8 +
          (35840 : K[X]) * b7 * (h0 ^ 4 * g1) ^ 3 * (h0 ^ 2) ^ 7 -
          (10240 : K[X]) * a6 ^ 3 * (h0 ^ 2) ^ 12 +
          (49920 : K[X]) * a6 ^ 2 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 8 -
          (25600 : K[X]) * a6 * (h0 ^ 4 * g1) ^ 4 * (h0 ^ 2) ^ 4 +
          (2800 : K[X]) * (h0 ^ 4 * g1) ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * (h0 ^ 2) ^ 19 -
              (3072 : K[X]) * a5 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 15 -
              (1536 : K[X]) * a6 ^ 2 * (h0 ^ 2) ^ 15 +
              (3840 : K[X]) * a6 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 11 -
              (1120 : K[X]) * (h0 ^ 4 * g1) ^ 4 * (h0 ^ 2) ^ 7) =
        Polynomial.C κ₅ * (h0 ^ 2) ^ 21 := by
    simpa only [alignedSixthDefect810, hHsq, hg] using hG
  apply mul_left_cancel₀ (pow_ne_zero 24 hh0)
  linear_combination hG'

/-- Consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `56 (8 p₅ h₀⁴ - 12 p₆ g₁ + 5 g₁³)`, eliminates
`q₇` from the square-chamber sixth core: the cleared sixth row of the
square chamber, with the root sextic visible at `h₀ = 0`. -/
theorem alignedSquareSixth_solved_810 {K : Type*} [Field K] [CharZero K]
    {h0 g1 a2 a3 a4 a5 a6 b4 b5 b6 b7 : K[X]} {κ κ₅ μ : K}
    (hcore :
      (81920 : K[X]) * a2 * h0 ^ 16 - (65536 : K[X]) * b4 * h0 ^ 14 -
          (30720 : K[X]) * a3 * g1 * h0 ^ 12 +
          (40960 : K[X]) * b5 * g1 * h0 ^ 10 -
          (40960 : K[X]) * a4 * a6 * h0 ^ 8 +
          (49152 : K[X]) * b6 * a6 * h0 ^ 6 +
          (25600 : K[X]) * a4 * g1 ^ 2 * h0 ^ 8 -
          (36864 : K[X]) * b6 * g1 ^ 2 * h0 ^ 6 -
          (61440 : K[X]) * a5 ^ 2 * h0 ^ 8 +
          (57344 : K[X]) * a5 * b7 * h0 ^ 6 +
          (46080 : K[X]) * a5 * a6 * g1 * h0 ^ 4 -
          (86016 : K[X]) * b7 * a6 * g1 * h0 ^ 2 -
          (21760 : K[X]) * a5 * g1 ^ 3 * h0 ^ 4 +
          (35840 : K[X]) * b7 * g1 ^ 3 * h0 ^ 2 -
          (10240 : K[X]) * a6 ^ 3 + (49920 : K[X]) * a6 ^ 2 * g1 ^ 2 -
          (25600 : K[X]) * a6 * g1 ^ 4 + (2800 : K[X]) * g1 ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * h0 ^ 14 -
              (3072 : K[X]) * a5 * g1 * h0 ^ 10 -
              (1536 : K[X]) * a6 ^ 2 * h0 ^ 6 +
              (3840 : K[X]) * a6 * g1 ^ 2 * h0 ^ 6 -
              (1120 : K[X]) * g1 ^ 4 * h0 ^ 6) =
        Polynomial.C κ₅ * h0 ^ 18)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    (81920 : K[X]) * a2 * h0 ^ 16 - (65536 : K[X]) * b4 * h0 ^ 14 -
        (30720 : K[X]) * a3 * g1 * h0 ^ 12 +
        (40960 : K[X]) * b5 * g1 * h0 ^ 10 -
        (40960 : K[X]) * a4 * a6 * h0 ^ 8 +
        (25600 : K[X]) * a4 * g1 ^ 2 * h0 ^ 8 +
        (10240 : K[X]) * a5 ^ 2 * h0 ^ 8 +
        (49152 : K[X]) * b6 * a6 * h0 ^ 6 -
        (36864 : K[X]) * b6 * g1 ^ 2 * h0 ^ 6 -
        (43520 : K[X]) * a5 * a6 * g1 * h0 ^ 4 +
        (20800 : K[X]) * a5 * g1 ^ 3 * h0 ^ 4 -
        (10240 : K[X]) * a6 ^ 3 + (23040 : K[X]) * a6 ^ 2 * g1 ^ 2 -
        (11040 : K[X]) * a6 * g1 ^ 4 + (1400 : K[X]) * g1 ^ 6 +
        Polynomial.C κ *
          ((2048 : K[X]) * a4 * h0 ^ 14 -
            (1280 : K[X]) * a5 * g1 * h0 ^ 10 -
            (1536 : K[X]) * a6 ^ 2 * h0 ^ 6 +
            (1152 : K[X]) * a6 * g1 ^ 2 * h0 ^ 6) -
        Polynomial.C μ *
          ((448 : K[X]) * a5 * h0 ^ 13 -
            (672 : K[X]) * a6 * g1 * h0 ^ 9 +
            (280 : K[X]) * g1 ^ 3 * h0 ^ 9) =
      Polynomial.C κ₅ * h0 ^ 18 := by
  linear_combination hcore -
    ((448 : K[X]) * a5 * h0 ^ 4 - (672 : K[X]) * a6 * g1 +
      (280 : K[X]) * g1 ^ 3) * hq7

/-- Factored transport form of the cleared square-chamber sixth row:
the sextic block `40 (35 g₁⁶ - 276 p₆ g₁⁴ + 576 p₆² g₁² - 256 p₆³)` is
an exact `h₀²`-multiple. -/
theorem alignedSquareSixth_factored_810 {K : Type*} [Field K] [CharZero K]
    {h0 g1 a2 a3 a4 a5 a6 b4 b5 b6 : K[X]} {κ κ₅ μ : K}
    (hsolved :
      (81920 : K[X]) * a2 * h0 ^ 16 - (65536 : K[X]) * b4 * h0 ^ 14 -
          (30720 : K[X]) * a3 * g1 * h0 ^ 12 +
          (40960 : K[X]) * b5 * g1 * h0 ^ 10 -
          (40960 : K[X]) * a4 * a6 * h0 ^ 8 +
          (25600 : K[X]) * a4 * g1 ^ 2 * h0 ^ 8 +
          (10240 : K[X]) * a5 ^ 2 * h0 ^ 8 +
          (49152 : K[X]) * b6 * a6 * h0 ^ 6 -
          (36864 : K[X]) * b6 * g1 ^ 2 * h0 ^ 6 -
          (43520 : K[X]) * a5 * a6 * g1 * h0 ^ 4 +
          (20800 : K[X]) * a5 * g1 ^ 3 * h0 ^ 4 -
          (10240 : K[X]) * a6 ^ 3 + (23040 : K[X]) * a6 ^ 2 * g1 ^ 2 -
          (11040 : K[X]) * a6 * g1 ^ 4 + (1400 : K[X]) * g1 ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * h0 ^ 14 -
              (1280 : K[X]) * a5 * g1 * h0 ^ 10 -
              (1536 : K[X]) * a6 ^ 2 * h0 ^ 6 +
              (1152 : K[X]) * a6 * g1 ^ 2 * h0 ^ 6) -
          Polynomial.C μ *
            ((448 : K[X]) * a5 * h0 ^ 13 -
              (672 : K[X]) * a6 * g1 * h0 ^ 9 +
              (280 : K[X]) * g1 ^ 3 * h0 ^ 9) =
        Polynomial.C κ₅ * h0 ^ 18) :
    (40 : K[X]) *
        ((35 : K[X]) * g1 ^ 6 - (276 : K[X]) * a6 * g1 ^ 4 +
          (576 : K[X]) * a6 ^ 2 * g1 ^ 2 - (256 : K[X]) * a6 ^ 3) =
      h0 ^ 2 *
        (Polynomial.C κ₅ * h0 ^ 16 -
          ((81920 : K[X]) * a2 * h0 ^ 14 - (65536 : K[X]) * b4 * h0 ^ 12 -
            (30720 : K[X]) * a3 * g1 * h0 ^ 10 +
            (40960 : K[X]) * b5 * g1 * h0 ^ 8 -
            (40960 : K[X]) * a4 * a6 * h0 ^ 6 +
            (25600 : K[X]) * a4 * g1 ^ 2 * h0 ^ 6 +
            (10240 : K[X]) * a5 ^ 2 * h0 ^ 6 +
            (49152 : K[X]) * b6 * a6 * h0 ^ 4 -
            (36864 : K[X]) * b6 * g1 ^ 2 * h0 ^ 4 -
            (43520 : K[X]) * a5 * a6 * g1 * h0 ^ 2 +
            (20800 : K[X]) * a5 * g1 ^ 3 * h0 ^ 2 +
            Polynomial.C κ *
              ((2048 : K[X]) * a4 * h0 ^ 12 -
                (1280 : K[X]) * a5 * g1 * h0 ^ 8 -
                (1536 : K[X]) * a6 ^ 2 * h0 ^ 4 +
                (1152 : K[X]) * a6 * g1 ^ 2 * h0 ^ 4) -
            Polynomial.C μ *
              ((448 : K[X]) * a5 * h0 ^ 11 -
                (672 : K[X]) * a6 * g1 * h0 ^ 7 +
                (280 : K[X]) * g1 ^ 3 * h0 ^ 7))) := by
  linear_combination hsolved

/-! ## Nonsquare chamber -/

/-- Peeling `H¹²` from `G = κ₅ H²¹` on `p₇ = H² g₂` leaves the
nonsquare-chamber sixth core.  The even exponent forces nothing:
`κ₅` is preserved, not cleared. -/
theorem alignedNonsquareSixth_core_810 {K : Type*} [Field K] [CharZero K]
    {H g2 a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 : K[X]} {κ κ₅ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hG : alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 21) :
    (81920 : K[X]) * a2 * H ^ 8 - (65536 : K[X]) * b4 * H ^ 7 -
        (30720 : K[X]) * a3 * g2 * H ^ 6 +
        (40960 : K[X]) * b5 * g2 * H ^ 5 -
        (40960 : K[X]) * a4 * a6 * H ^ 4 +
        (49152 : K[X]) * b6 * a6 * H ^ 3 +
        (25600 : K[X]) * a4 * g2 ^ 2 * H ^ 4 -
        (36864 : K[X]) * b6 * g2 ^ 2 * H ^ 3 -
        (61440 : K[X]) * a5 ^ 2 * H ^ 4 +
        (57344 : K[X]) * a5 * b7 * H ^ 3 +
        (46080 : K[X]) * a5 * a6 * g2 * H ^ 2 -
        (86016 : K[X]) * b7 * a6 * g2 * H -
        (21760 : K[X]) * a5 * g2 ^ 3 * H ^ 2 +
        (35840 : K[X]) * b7 * g2 ^ 3 * H -
        (10240 : K[X]) * a6 ^ 3 + (49920 : K[X]) * a6 ^ 2 * g2 ^ 2 -
        (25600 : K[X]) * a6 * g2 ^ 4 + (2800 : K[X]) * g2 ^ 6 +
        Polynomial.C κ *
          ((2048 : K[X]) * a4 * H ^ 7 -
            (3072 : K[X]) * a5 * g2 * H ^ 5 -
            (1536 : K[X]) * a6 ^ 2 * H ^ 3 +
            (3840 : K[X]) * a6 * g2 ^ 2 * H ^ 3 -
            (1120 : K[X]) * g2 ^ 4 * H ^ 3) =
      Polynomial.C κ₅ * H ^ 9 := by
  have hG' :
      (81920 : K[X]) * a2 * H ^ 20 - (65536 : K[X]) * b4 * H ^ 19 -
          (30720 : K[X]) * a3 * (H ^ 2 * g2) * H ^ 16 +
          (40960 : K[X]) * b5 * (H ^ 2 * g2) * H ^ 15 -
          (40960 : K[X]) * a4 * a6 * H ^ 16 +
          (49152 : K[X]) * b6 * a6 * H ^ 15 +
          (25600 : K[X]) * a4 * (H ^ 2 * g2) ^ 2 * H ^ 12 -
          (36864 : K[X]) * b6 * (H ^ 2 * g2) ^ 2 * H ^ 11 -
          (61440 : K[X]) * a5 ^ 2 * H ^ 16 +
          (57344 : K[X]) * a5 * b7 * H ^ 15 +
          (46080 : K[X]) * a5 * a6 * (H ^ 2 * g2) * H ^ 12 -
          (86016 : K[X]) * b7 * a6 * (H ^ 2 * g2) * H ^ 11 -
          (21760 : K[X]) * a5 * (H ^ 2 * g2) ^ 3 * H ^ 8 +
          (35840 : K[X]) * b7 * (H ^ 2 * g2) ^ 3 * H ^ 7 -
          (10240 : K[X]) * a6 ^ 3 * H ^ 12 +
          (49920 : K[X]) * a6 ^ 2 * (H ^ 2 * g2) ^ 2 * H ^ 8 -
          (25600 : K[X]) * a6 * (H ^ 2 * g2) ^ 4 * H ^ 4 +
          (2800 : K[X]) * (H ^ 2 * g2) ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * H ^ 19 -
              (3072 : K[X]) * a5 * (H ^ 2 * g2) * H ^ 15 -
              (1536 : K[X]) * a6 ^ 2 * H ^ 15 +
              (3840 : K[X]) * a6 * (H ^ 2 * g2) ^ 2 * H ^ 11 -
              (1120 : K[X]) * (H ^ 2 * g2) ^ 4 * H ^ 7) =
        Polynomial.C κ₅ * H ^ 21 := by
    simpa only [alignedSixthDefect810, hg2] using hG
  apply mul_left_cancel₀ (pow_ne_zero 12 hH)
  linear_combination hG'

/-- Consuming the previous factored quotient (`128 q₇ H` solved) with
the same mate eliminates `q₇` from the nonsquare-chamber sixth core:
the cleared sixth row of the nonsquare chamber. -/
theorem alignedNonsquareSixth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a2 a3 a4 a5 a6 b4 b5 b6 b7 : K[X]} {κ κ₅ : K}
    (hcore :
      (81920 : K[X]) * a2 * H ^ 8 - (65536 : K[X]) * b4 * H ^ 7 -
          (30720 : K[X]) * a3 * g2 * H ^ 6 +
          (40960 : K[X]) * b5 * g2 * H ^ 5 -
          (40960 : K[X]) * a4 * a6 * H ^ 4 +
          (49152 : K[X]) * b6 * a6 * H ^ 3 +
          (25600 : K[X]) * a4 * g2 ^ 2 * H ^ 4 -
          (36864 : K[X]) * b6 * g2 ^ 2 * H ^ 3 -
          (61440 : K[X]) * a5 ^ 2 * H ^ 4 +
          (57344 : K[X]) * a5 * b7 * H ^ 3 +
          (46080 : K[X]) * a5 * a6 * g2 * H ^ 2 -
          (86016 : K[X]) * b7 * a6 * g2 * H -
          (21760 : K[X]) * a5 * g2 ^ 3 * H ^ 2 +
          (35840 : K[X]) * b7 * g2 ^ 3 * H -
          (10240 : K[X]) * a6 ^ 3 + (49920 : K[X]) * a6 ^ 2 * g2 ^ 2 -
          (25600 : K[X]) * a6 * g2 ^ 4 + (2800 : K[X]) * g2 ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * H ^ 7 -
              (3072 : K[X]) * a5 * g2 * H ^ 5 -
              (1536 : K[X]) * a6 ^ 2 * H ^ 3 +
              (3840 : K[X]) * a6 * g2 ^ 2 * H ^ 3 -
              (1120 : K[X]) * g2 ^ 4 * H ^ 3) =
        Polynomial.C κ₅ * H ^ 9)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    (81920 : K[X]) * a2 * H ^ 8 - (65536 : K[X]) * b4 * H ^ 7 -
        (30720 : K[X]) * a3 * g2 * H ^ 6 +
        (40960 : K[X]) * b5 * g2 * H ^ 5 -
        (40960 : K[X]) * a4 * a6 * H ^ 4 +
        (25600 : K[X]) * a4 * g2 ^ 2 * H ^ 4 +
        (10240 : K[X]) * a5 ^ 2 * H ^ 4 +
        (49152 : K[X]) * b6 * a6 * H ^ 3 -
        (36864 : K[X]) * b6 * g2 ^ 2 * H ^ 3 -
        (43520 : K[X]) * a5 * a6 * g2 * H ^ 2 +
        (20800 : K[X]) * a5 * g2 ^ 3 * H ^ 2 -
        (10240 : K[X]) * a6 ^ 3 + (23040 : K[X]) * a6 ^ 2 * g2 ^ 2 -
        (11040 : K[X]) * a6 * g2 ^ 4 + (1400 : K[X]) * g2 ^ 6 +
        Polynomial.C κ *
          ((2048 : K[X]) * a4 * H ^ 7 -
            (1280 : K[X]) * a5 * g2 * H ^ 5 -
            (1536 : K[X]) * a6 ^ 2 * H ^ 3 +
            (1152 : K[X]) * a6 * g2 ^ 2 * H ^ 3) =
      Polynomial.C κ₅ * H ^ 9 := by
  linear_combination hcore -
    ((448 : K[X]) * a5 * H ^ 2 - (672 : K[X]) * a6 * g2 +
      (280 : K[X]) * g2 ^ 3) * hfac

/-- Factored transport form of the cleared nonsquare-chamber sixth row:
the sextic block is an exact `H`-multiple. -/
theorem alignedNonsquareSixth_factored_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a2 a3 a4 a5 a6 b4 b5 b6 : K[X]} {κ κ₅ : K}
    (hsolved :
      (81920 : K[X]) * a2 * H ^ 8 - (65536 : K[X]) * b4 * H ^ 7 -
          (30720 : K[X]) * a3 * g2 * H ^ 6 +
          (40960 : K[X]) * b5 * g2 * H ^ 5 -
          (40960 : K[X]) * a4 * a6 * H ^ 4 +
          (25600 : K[X]) * a4 * g2 ^ 2 * H ^ 4 +
          (10240 : K[X]) * a5 ^ 2 * H ^ 4 +
          (49152 : K[X]) * b6 * a6 * H ^ 3 -
          (36864 : K[X]) * b6 * g2 ^ 2 * H ^ 3 -
          (43520 : K[X]) * a5 * a6 * g2 * H ^ 2 +
          (20800 : K[X]) * a5 * g2 ^ 3 * H ^ 2 -
          (10240 : K[X]) * a6 ^ 3 + (23040 : K[X]) * a6 ^ 2 * g2 ^ 2 -
          (11040 : K[X]) * a6 * g2 ^ 4 + (1400 : K[X]) * g2 ^ 6 +
          Polynomial.C κ *
            ((2048 : K[X]) * a4 * H ^ 7 -
              (1280 : K[X]) * a5 * g2 * H ^ 5 -
              (1536 : K[X]) * a6 ^ 2 * H ^ 3 +
              (1152 : K[X]) * a6 * g2 ^ 2 * H ^ 3) =
        Polynomial.C κ₅ * H ^ 9) :
    (40 : K[X]) *
        ((35 : K[X]) * g2 ^ 6 - (276 : K[X]) * a6 * g2 ^ 4 +
          (576 : K[X]) * a6 ^ 2 * g2 ^ 2 - (256 : K[X]) * a6 ^ 3) =
      H *
        (Polynomial.C κ₅ * H ^ 8 -
          ((81920 : K[X]) * a2 * H ^ 7 - (65536 : K[X]) * b4 * H ^ 6 -
            (30720 : K[X]) * a3 * g2 * H ^ 5 +
            (40960 : K[X]) * b5 * g2 * H ^ 4 -
            (40960 : K[X]) * a4 * a6 * H ^ 3 +
            (25600 : K[X]) * a4 * g2 ^ 2 * H ^ 3 +
            (10240 : K[X]) * a5 ^ 2 * H ^ 3 +
            (49152 : K[X]) * b6 * a6 * H ^ 2 -
            (36864 : K[X]) * b6 * g2 ^ 2 * H ^ 2 -
            (43520 : K[X]) * a5 * a6 * g2 * H +
            (20800 : K[X]) * a5 * g2 ^ 3 * H +
            Polynomial.C κ *
              ((2048 : K[X]) * a4 * H ^ 6 -
                (1280 : K[X]) * a5 * g2 * H ^ 4 -
                (1536 : K[X]) * a6 ^ 2 * H ^ 2 +
                (1152 : K[X]) * a6 * g2 ^ 2 * H ^ 2))) := by
  linear_combination hsolved

/-! ## Source-facing sixth-row packets -/

/-- Source-facing weight-forty-two integral of a normalized aligned
scale-two `(8,10)` source: the degree-`11` row is consumed into the
chamber-free `G = κ₅ H²¹` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedSixthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 35 ∧
        alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 21 := by
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
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  exact ⟨κ, κ₃, κ₄, κ₅, aligned_q9_solved_810 haligned, hM, hE4, hF2, hG⟩

/-- Exact square-chamber sixth packet of a normalized aligned scale-two
`(8,10)` source: on top of `p₇ = h₀⁴ g₁`, `q₉ = (5/4) g₁ h₀⁶`, and the
previous packet, the consumed degree-`11` row gives the cleared sixth
row (with `p₂` at `h₀¹⁶` and `q₄` at `h₀¹⁴`), the carried root
collapse `g₁ = p₆ = 0`, and the carried descents `h₀ ∣ g₁`,
`h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedSixthFace_squareChamber_packet
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
    ∃ (κ μ κ₅ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        (81920 : K[X]) * p.coeff 2 * h0 ^ 16 -
            (65536 : K[X]) * q.coeff 4 * h0 ^ 14 -
            (30720 : K[X]) * p.coeff 3 * g1 * h0 ^ 12 +
            (40960 : K[X]) * q.coeff 5 * g1 * h0 ^ 10 -
            (40960 : K[X]) * p.coeff 4 * p.coeff 6 * h0 ^ 8 +
            (25600 : K[X]) * p.coeff 4 * g1 ^ 2 * h0 ^ 8 +
            (10240 : K[X]) * p.coeff 5 ^ 2 * h0 ^ 8 +
            (49152 : K[X]) * q.coeff 6 * p.coeff 6 * h0 ^ 6 -
            (36864 : K[X]) * q.coeff 6 * g1 ^ 2 * h0 ^ 6 -
            (43520 : K[X]) * p.coeff 5 * p.coeff 6 * g1 * h0 ^ 4 +
            (20800 : K[X]) * p.coeff 5 * g1 ^ 3 * h0 ^ 4 -
            (10240 : K[X]) * p.coeff 6 ^ 3 +
            (23040 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 2 -
            (11040 : K[X]) * p.coeff 6 * g1 ^ 4 +
            (1400 : K[X]) * g1 ^ 6 +
            Polynomial.C κ *
              ((2048 : K[X]) * p.coeff 4 * h0 ^ 14 -
                (1280 : K[X]) * p.coeff 5 * g1 * h0 ^ 10 -
                (1536 : K[X]) * p.coeff 6 ^ 2 * h0 ^ 6 +
                (1152 : K[X]) * p.coeff 6 * g1 ^ 2 * h0 ^ 6) -
            Polynomial.C μ *
              ((448 : K[X]) * p.coeff 5 * h0 ^ 13 -
                (672 : K[X]) * p.coeff 6 * g1 * h0 ^ 9 +
                (280 : K[X]) * g1 ^ 3 * h0 ^ 9) =
          Polynomial.C κ₅ * h0 ^ 18 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 := by
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
  have hsolved4 := alignedSquareFourth_solved_810 hcore4 hcore
  have hcollapse : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedSquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
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
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore6 := alignedSquareSixth_core_810 hh0 hHsq hp7 hG
  have hsolved6 := alignedSquareSixth_solved_810 hcore6 hcore
  exact ⟨κ, μ, κ₅, g1, hp7, by rw [hq9, hg, hg1, hHsq]; ring,
    hsolved6, hcollapse, hdvdg1, hdvdp6⟩

/-- Exact nonsquare-chamber sixth packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = H² g₂` and the previous
packet, the consumed degree-`11` row gives the cleared sixth row (with
`p₂` at `H⁸` and `q₄` at `H⁷`), the carried root collapse
`g₂ = p₆ = 0` at every (simple) root of the core, and the carried
descents `H ∣ g₂`, `H ∣ p₆`.  Unlike the odd rows, `κ₅` is not
forced to vanish here. -/
theorem normalized810ScaleTwo_alignedSixthFace_nonsquareChamber_packet
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
    ∃ (κ κ₅ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        (81920 : K[X]) * p.coeff 2 * H ^ 8 -
            (65536 : K[X]) * q.coeff 4 * H ^ 7 -
            (30720 : K[X]) * p.coeff 3 * g2 * H ^ 6 +
            (40960 : K[X]) * q.coeff 5 * g2 * H ^ 5 -
            (40960 : K[X]) * p.coeff 4 * p.coeff 6 * H ^ 4 +
            (25600 : K[X]) * p.coeff 4 * g2 ^ 2 * H ^ 4 +
            (10240 : K[X]) * p.coeff 5 ^ 2 * H ^ 4 +
            (49152 : K[X]) * q.coeff 6 * p.coeff 6 * H ^ 3 -
            (36864 : K[X]) * q.coeff 6 * g2 ^ 2 * H ^ 3 -
            (43520 : K[X]) * p.coeff 5 * p.coeff 6 * g2 * H ^ 2 +
            (20800 : K[X]) * p.coeff 5 * g2 ^ 3 * H ^ 2 -
            (10240 : K[X]) * p.coeff 6 ^ 3 +
            (23040 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 2 -
            (11040 : K[X]) * p.coeff 6 * g2 ^ 4 +
            (1400 : K[X]) * g2 ^ 6 +
            Polynomial.C κ *
              ((2048 : K[X]) * p.coeff 4 * H ^ 7 -
                (1280 : K[X]) * p.coeff 5 * g2 * H ^ 5 -
                (1536 : K[X]) * p.coeff 6 ^ 2 * H ^ 3 +
                (1152 : K[X]) * p.coeff 6 * g2 ^ 2 * H ^ 3) =
          Polynomial.C κ₅ * H ^ 9 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 := by
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
  have hsolved4 := alignedNonsquareFourth_solved_810 hcore4 hfac
  have hcollapse : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedNonsquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero
      hHdegree hnsq ha
  have hdvdg2 : H ∣ g2 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).1)
  have hdvdp6 : H ∣ p.coeff 6 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).2)
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore6 := alignedNonsquareSixth_core_810 hH hg2 hG
  have hsolved6 := alignedNonsquareSixth_solved_810 hcore6 hfac
  exact ⟨κ, κ₅, g2, hg2, by rw [hq9, hg2]; ring, hsolved6,
    hcollapse, hdvdg2, hdvdp6⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`11`
aligned row, carrying the factored transport of the sextic block.
Neither chamber is excluded, the constants `κ`, `μ`, `κ₅` are
preserved, and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedSixthFace_chamberDichotomy
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
      ∃ (κ μ κ₅ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (40 : K[X]) *
              ((35 : K[X]) * g1 ^ 6 - (276 : K[X]) * p.coeff 6 * g1 ^ 4 +
                (576 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 2 -
                (256 : K[X]) * p.coeff 6 ^ 3) =
            h0 ^ 2 *
              (Polynomial.C κ₅ * h0 ^ 16 -
                ((81920 : K[X]) * p.coeff 2 * h0 ^ 14 -
                  (65536 : K[X]) * q.coeff 4 * h0 ^ 12 -
                  (30720 : K[X]) * p.coeff 3 * g1 * h0 ^ 10 +
                  (40960 : K[X]) * q.coeff 5 * g1 * h0 ^ 8 -
                  (40960 : K[X]) * p.coeff 4 * p.coeff 6 * h0 ^ 6 +
                  (25600 : K[X]) * p.coeff 4 * g1 ^ 2 * h0 ^ 6 +
                  (10240 : K[X]) * p.coeff 5 ^ 2 * h0 ^ 6 +
                  (49152 : K[X]) * q.coeff 6 * p.coeff 6 * h0 ^ 4 -
                  (36864 : K[X]) * q.coeff 6 * g1 ^ 2 * h0 ^ 4 -
                  (43520 : K[X]) * p.coeff 5 * p.coeff 6 * g1 * h0 ^ 2 +
                  (20800 : K[X]) * p.coeff 5 * g1 ^ 3 * h0 ^ 2 +
                  Polynomial.C κ *
                    ((2048 : K[X]) * p.coeff 4 * h0 ^ 12 -
                      (1280 : K[X]) * p.coeff 5 * g1 * h0 ^ 8 -
                      (1536 : K[X]) * p.coeff 6 ^ 2 * h0 ^ 4 +
                      (1152 : K[X]) * p.coeff 6 * g1 ^ 2 * h0 ^ 4) -
                  Polynomial.C μ *
                    ((448 : K[X]) * p.coeff 5 * h0 ^ 11 -
                      (672 : K[X]) * p.coeff 6 * g1 * h0 ^ 7 +
                      (280 : K[X]) * g1 ^ 3 * h0 ^ 7))) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ κ₅ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (40 : K[X]) *
              ((35 : K[X]) * g2 ^ 6 - (276 : K[X]) * p.coeff 6 * g2 ^ 4 +
                (576 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 2 -
                (256 : K[X]) * p.coeff 6 ^ 3) =
            H *
              (Polynomial.C κ₅ * H ^ 8 -
                ((81920 : K[X]) * p.coeff 2 * H ^ 7 -
                  (65536 : K[X]) * q.coeff 4 * H ^ 6 -
                  (30720 : K[X]) * p.coeff 3 * g2 * H ^ 5 +
                  (40960 : K[X]) * q.coeff 5 * g2 * H ^ 4 -
                  (40960 : K[X]) * p.coeff 4 * p.coeff 6 * H ^ 3 +
                  (25600 : K[X]) * p.coeff 4 * g2 ^ 2 * H ^ 3 +
                  (10240 : K[X]) * p.coeff 5 ^ 2 * H ^ 3 +
                  (49152 : K[X]) * q.coeff 6 * p.coeff 6 * H ^ 2 -
                  (36864 : K[X]) * q.coeff 6 * g2 ^ 2 * H ^ 2 -
                  (43520 : K[X]) * p.coeff 5 * p.coeff 6 * g2 * H +
                  (20800 : K[X]) * p.coeff 5 * g2 ^ 3 * H +
                  Polynomial.C κ *
                    ((2048 : K[X]) * p.coeff 4 * H ^ 6 -
                      (1280 : K[X]) * p.coeff 5 * g2 * H ^ 4 -
                      (1536 : K[X]) * p.coeff 6 ^ 2 * H ^ 2 +
                      (1152 : K[X]) * p.coeff 6 * g2 ^ 2 * H ^ 2))) ∧
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
      normalized810ScaleTwo_alignedSixthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₅, g1, hp7, hq9, hsolved6, hcollapse,
      hdvdg1, hdvdp6⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, κ₅, g1, hp7, hq9,
      alignedSquareSixth_factored_810 hsolved6,
      hcollapse, hdvdg1, hdvdp6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedSixthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₅, g2, hp7, hq9, hsolved6, hcollapse,
      hdvdg2, hdvdp6⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, κ₅, g2, hp7, hq9,
      alignedNonsquareSixth_factored_810 hsolved6,
      hcollapse, hdvdg2, hdvdp6⟩

/-- Chamber-independent root jet after the consumed degree-`11` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its sextic content is absorbed by the
degree-`13` collapse (`alignedSixth_rootSextic_absorbed_810`) — and
the new coefficients `p₂, q₄` are tied into the cleared sixth row
instead of being killed. -/
theorem normalized810ScaleTwo_alignedSixthFace_rootJet
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
      (p.coeff 6).eval a = 0 :=
  normalized810ScaleTwo_alignedFifthFace_rootJet hsource haligned

#print axioms alignedSixthCoefficientJacobianRow_810
#print axioms alignedSixthDefect_weightedDerivative_identity_810
#print axioms alignedSixthDefectRow_eq_zero_810
#print axioms alignedSixthDefectPowerRelation_810
#print axioms alignedSixth_factored_rootSextic_810
#print axioms alignedSixth_rootSextic_absorbed_810
#print axioms alignedSquareSixth_core_810
#print axioms alignedSquareSixth_solved_810
#print axioms alignedSquareSixth_factored_810
#print axioms alignedNonsquareSixth_core_810
#print axioms alignedNonsquareSixth_solved_810
#print axioms alignedNonsquareSixth_factored_810
#print axioms normalized810ScaleTwo_alignedSixthFace_packet
#print axioms normalized810ScaleTwo_alignedSixthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedSixthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedSixthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedSixthFace_rootJet

end Max11DegreeRoutes
