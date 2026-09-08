import Fable810ScaleTwoAlignedThirdFaceScratch

/-! # Fourth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedThirdFaceScratch` consumed the degree-`13`
aligned Keller row of the normalized scale-two `(8,10)` source: the
chamber-free weight-twenty-eight integral `E = κ₃ H¹⁴`, the cleared
fourth rows, the root quartic `320 p₆² - 240 p₆ g² + 35 g⁴ = 0`, the
branch collapse `g(a) = 0 ∧ p₆(a) = 0`, and the deepened descents
`h₀ ∣ g₁, h₀ ∣ p₆` / `H ∣ g₂, H ∣ p₆`.  This file consumes the next
unused aligned row, the degree-`12` Jacobian coefficient — the first
row that sees `p₃` and `q₅` (internal names `alignedFifth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation
`C = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇² - κ H⁷ = 0`, the consumed degree-`14`
row `2 H D' - 21 D H' = 0`, and the consumed degree-`13` row
`H E' - 14 E H' = 0`, the degree-`12` row is the weighted derivative of
the weight-thirty-five defect

`F = 20480 p₃ H¹⁶ - 16384 q₅ H¹⁵ - 10240 p₄ p₇ H¹² + 12288 q₆ p₇ H¹¹
  - 12800 p₅ p₆ H¹² + 14336 p₆ q₇ H¹¹ + 8800 p₅ p₇² H⁸
  - 11648 q₇ p₇² H⁷ - 8320 p₆² p₇ H⁸ + 6760 p₆ p₇³ H⁴ - 819 p₇⁵
  + κ (512 p₅ H¹⁵ - 832 p₆ p₇ H¹¹ + 364 p₇³ H⁷)`,

via the exact multiplier identity

`4096 H¹² · row₁₂[p₈ = H⁴, q₁₀ = H⁵] = (2 H F' - 35 F H')
  - 9216 H¹² p₄' N + 4096 H¹² p₄ N'
  + (1024 H⁹ p₅' + 1920 p₅ H⁸ H') C - 640 H⁹ p₅ C'
  + (208 p₆ H⁴ + 91 p₇²) (2 H D' - 21 D H') + 26 p₇ (H E' - 14 E H')`.

On the aligned face every right-hand correction vanishes, so
`2 H F' = 35 F H'` and the squared weight-thirty-five first integral

`F² = κ₄ H³⁵`

holds for a preserved constant `κ₄`.  The odd exponent splits honestly
on the chambers of the previous packet, exactly as the degree-`14` row
did:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: the integral has a
  polynomial square root `F = ν h₀³⁵` with `ν² = κ₄`.  Peeling `h₀²⁰`
  and consuming the previous factored quotient (`128 q₇ h₀²` solved,
  transported by the mate `112 p₆ - 91 g₁²`) leaves the cleared fifth
  row
  `20480 p₃ h₀¹² - 16384 q₅ h₀¹⁰ - 10240 p₄ g₁ h₀⁸ + 12288 q₆ g₁ h₀⁶
   + 5120 p₅ p₆ h₀⁴ - 5760 p₅ g₁² h₀⁴ - 3840 p₆² g₁ + 2560 p₆ g₁³
   - 364 g₁⁵ + κ (512 p₅ h₀¹⁰ - 384 p₆ g₁ h₀⁶)
   - μ (112 p₆ - 91 g₁²) h₀⁹ = ν h₀¹⁵`
  with the factored transport form
  `4 g₁ (960 p₆² - 640 p₆ g₁² + 91 g₁⁴) = h₀⁴ · (co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₄ = 0` and `F = 0` identically; with `p₇ = H² g₂`,
  peeling `H¹⁰` and consuming the previous factored quotient (same mate
  `112 p₆ - 91 g₂²`) leaves
  `20480 p₃ H⁶ - 16384 q₅ H⁵ - 10240 p₄ g₂ H⁴ + 12288 q₆ g₂ H³
   + 5120 p₅ p₆ H² - 5760 p₅ g₂² H² - 3840 p₆² g₂ + 2560 p₆ g₂³
   - 364 g₂⁵ + κ (512 p₅ H⁵ - 384 p₆ g₂ H³) = 0`
  with the factored transport form
  `4 g₂ (960 p₆² - 640 p₆ g₂² + 91 g₂⁴) = H² · (co-factor)`.

At a root of the core the factored transport leaves the honest quintic
branch `g = 0 ∨ 960 p₆² - 640 p₆ g² + 91 g⁴ = 0`.  Unlike the previous
two rows this adds *no new* root information: the consumed degree-`13`
row already collapsed `g(a) = 0 ∧ p₆(a) = 0` at every core root, and
that collapse absorbs the quintic identically
(`alignedFifth_rootQuintic_absorbed_810`).  The chamber-independent
root jet therefore stays `p₇, q₉, q₈, p₆` — the row ties the new
coefficients `p₃, q₅` into the cleared fifth row (at `h₀¹²`/`h₀¹⁰`,
resp. `H⁶`/`H⁵`) instead of killing anything new at the root.

The generic transfer lemmas are reused unchanged:
`dvd_of_sq_dvd_sq_poly`, `nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`linearPolynomial_dvd_of_eval_eq_zero_810` (all generic in the degree
pair).  No closure is claimed.  Both chambers remain open, the
constants `κ`, `μ`, `κ₃`, `κ₄ = ν²` are preserved where not forced, the
zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`,
`κ₄ = 0`, `ν = 0`) are not excluded as polynomial identities, the
deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H` from the previous
face are still not re-cleared through the tower here, the quintic
branch `960 p₆² - 640 p₆ g² + 91 g⁴ = 0` is recorded but not excluded,
and no individual vanishing of `p₃`, `p₄`, `p₅`, `q₅`, `q₆`, `q₇` is
claimed.  The next unused Keller row on the aligned face is the
degree-`11` Jacobian coefficient, the first row that sees `p₂` and
`q₄` (weight-forty-two defect, even exponent, hence chamber-free).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`12` Keller coefficient on the aligned face -/

/-- The fifth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`12` Jacobian coefficient, the first
aligned row that sees `p₃` and `q₅`. -/
theorem alignedFifthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 7).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 5).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 6).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 7).derivative +
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
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC5, hC6, hC7, hC8, hC9, hC10, hC4, hC3]
  linear_combination hcoeff

/-! ## Aligned fifth defect -/

/-- Weight-thirty-five defect of the degree-`12` aligned `(8,10)` row:
`F = 20480 p₃ H¹⁶ - 16384 q₅ H¹⁵ - 10240 p₄ p₇ H¹² + 12288 q₆ p₇ H¹¹
 - 12800 p₅ p₆ H¹² + 14336 p₆ q₇ H¹¹ + 8800 p₅ p₇² H⁸
 - 11648 q₇ p₇² H⁷ - 8320 p₆² p₇ H⁸ + 6760 p₆ p₇³ H⁴ - 819 p₇⁵
 + κ (512 p₅ H¹⁵ - 832 p₆ p₇ H¹¹ + 364 p₇³ H⁷)`.
On the aligned face its square is a polynomial first integral of odd
weight thirty-five. -/
def alignedFifthDefect810 {K : Type*} [CommRing K]
    (H a3 a4 a5 a6 a7 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (20480 : K[X]) * a3 * H ^ 16 - (16384 : K[X]) * b5 * H ^ 15 -
    (10240 : K[X]) * a4 * a7 * H ^ 12 +
    (12288 : K[X]) * b6 * a7 * H ^ 11 -
    (12800 : K[X]) * a5 * a6 * H ^ 12 +
    (14336 : K[X]) * a6 * b7 * H ^ 11 +
    (8800 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
    (11648 : K[X]) * b7 * a7 ^ 2 * H ^ 7 -
    (8320 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
    (6760 : K[X]) * a6 * a7 ^ 3 * H ^ 4 - (819 : K[X]) * a7 ^ 5 +
    Polynomial.C κ *
      ((512 : K[X]) * a5 * H ^ 15 - (832 : K[X]) * a6 * a7 * H ^ 11 +
        (364 : K[X]) * a7 ^ 3 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`12` Jacobian expression with the
weighted derivative of `F`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, and degree-`13` rows. -/
theorem alignedFifthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a3 a4 a5 a6 a7 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (4096 : K[X]) * H ^ 12 *
        ((H ^ 4).derivative * (b5 * (5 : K[X])) +
          a7.derivative * (b6 * (6 : K[X])) +
          a6.derivative * (b7 * (7 : K[X])) +
          a5.derivative * (b8 * (8 : K[X])) +
          a4.derivative * (b9 * (9 : K[X])) +
          a3.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b5.derivative +
          (a7 * (7 : K[X])) * b6.derivative +
          (a6 * (6 : K[X])) * b7.derivative +
          (a5 * (5 : K[X])) * b8.derivative +
          (a4 * (4 : K[X])) * b9.derivative +
          (a3 * (3 : K[X])) * (H ^ 5).derivative)) =
      ((2 : K[X]) * H *
          (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ).derivative -
        (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ *
          H.derivative) -
        (9216 : K[X]) * H ^ 12 * a4.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (4096 : K[X]) * H ^ 12 * a4 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((1024 : K[X]) * H ^ 9 * a5.derivative +
            (1920 : K[X]) * a5 * H ^ 8 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (640 : K[X]) * H ^ 9 * a5 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((208 : K[X]) * a6 * H ^ 4 + (91 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        (26 : K[X]) * a7 *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) := by
  simp only [alignedFifthDefect810, alignedFourthDefect810,
    alignedThirdDefect810, Polynomial.derivative_sub,
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

/-- On the aligned face, with the consumed degree-`15`, degree-`14`,
and degree-`13` rows, the degree-`12` row is the weighted derivative
`2 H F' - 35 F H' = 0`. -/
theorem alignedFifthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ).derivative -
      (35 : K[X]) *
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedFifthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  rw [hC5, hC6, hC7, hC8, hC9, hC10, hC4, hC3] at hrow
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
  have hid := alignedFifthDefect_weightedDerivative_identity_810
    H (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
    (q.coeff 5) (q.coeff 6) (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD, hrowE] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-thirty-five polynomial first integral of the aligned
`(8,10)` fifth defect: `F² = κ₄ H³⁵`. -/
theorem alignedFifthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₄ : K,
      alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
          (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₄ * H ^ 35 := by
  let F : K[X] :=
    alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * F.derivative -
        (35 : K[X]) * F * H.derivative = 0 := by
    simpa only [F] using
      alignedFifthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC35 : Polynomial.C (35 : K) = (35 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (F ^ 2) (H ^ 35) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      F ^ 2 * (Polynomial.C (35 : K) * H ^ (35 - 1) * H.derivative) -
          Polynomial.C (2 : K) * F ^ (2 - 1) * F.derivative * H ^ 35 =
          F * H ^ 34 *
            (Polynomial.C (35 : K) * F * H.derivative -
              Polynomial.C (2 : K) * H * F.derivative) := by
        ring
      _ = 0 := by
        rw [hC35, hC2]
        have hfac :
            (35 : K[X]) * F * H.derivative -
              (2 : K[X]) * H * F.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 35 hH) hW

/-! ## Root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport fifth row at a root of its
cofactor: either the descent quotient vanishes there, or the quintic
core `960 p₆² - 640 p₆ g² + 91 g⁴` does.  Neither branch is
excluded. -/
theorem alignedFifth_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (4 : K[X]) * g *
        ((960 : K[X]) * a6 ^ 2 - (640 : K[X]) * a6 * g ^ 2 +
          (91 : K[X]) * g ^ 4) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨
      960 * (a6.eval a) ^ 2 - 640 * a6.eval a * (g.eval a) ^ 2 +
        91 * (g.eval a) ^ 4 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h4g | hquad
  · exact Or.inl
      ((mul_eq_zero.mp h4g).resolve_left (by norm_num : (4 : K) ≠ 0))
  · exact Or.inr (by linear_combination hquad)

/-- The root quintic of the consumed degree-`12` row is absorbed by the
collapse of the previous face: at a root where `g` and `p₆` already
vanish it holds identically, so the fifth row adds no new root
constraint. -/
theorem alignedFifth_rootQuintic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    4 * G * (960 * P6 ^ 2 - 640 * P6 * G ^ 2 + 91 * G ^ 4) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Square chamber -/

/-- In the square chamber the weight-thirty-five integral has a
polynomial square root with square core: `F = ν h₀³⁵` with `ν² = κ₄`.
The constant `ν` is preserved, not cleared. -/
theorem alignedSquareFifth_sqrt_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a3 a4 a5 a6 a7 b5 b6 b7 : K[X]} {κ κ₄ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hF2 : alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₄ * H ^ 35) :
    ∃ ν : K, ν ^ 2 = κ₄ ∧
      alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ =
        Polynomial.C ν * h0 ^ 35 := by
  set F : K[X] := alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ
    with hFdef
  have hdvd : (h0 ^ 35) ^ 2 ∣ F ^ 2 := by
    refine ⟨Polynomial.C κ₄, ?_⟩
    rw [hF2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₄ := by
    have h70 := hF2
    rw [hG, hHsq] at h70
    apply mul_left_cancel₀ (pow_ne_zero 70 hh0)
    linear_combination h70
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₄
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν, ?_, ?_⟩
  · have hCν : Polynomial.C (ν ^ 2) = Polynomial.C κ₄ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

/-- Peeling `h₀²⁰` from `F = ν h₀³⁵` on `p₇ = h₀⁴ g₁` leaves the
square-chamber fifth core. -/
theorem alignedSquareFifth_core_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a3 a4 a5 a6 a7 b5 b6 b7 : K[X]} {κ ν : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hF : alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 35) :
    (20480 : K[X]) * a3 * h0 ^ 12 - (16384 : K[X]) * b5 * h0 ^ 10 -
        (10240 : K[X]) * a4 * g1 * h0 ^ 8 +
        (12288 : K[X]) * b6 * g1 * h0 ^ 6 -
        (12800 : K[X]) * a5 * a6 * h0 ^ 4 +
        (14336 : K[X]) * a6 * b7 * h0 ^ 2 +
        (8800 : K[X]) * a5 * g1 ^ 2 * h0 ^ 4 -
        (11648 : K[X]) * b7 * g1 ^ 2 * h0 ^ 2 -
        (8320 : K[X]) * a6 ^ 2 * g1 + (6760 : K[X]) * a6 * g1 ^ 3 -
        (819 : K[X]) * g1 ^ 5 +
        Polynomial.C κ *
          ((512 : K[X]) * a5 * h0 ^ 10 -
            (832 : K[X]) * a6 * g1 * h0 ^ 6 +
            (364 : K[X]) * g1 ^ 3 * h0 ^ 6) =
      Polynomial.C ν * h0 ^ 15 := by
  have hF' :
      (20480 : K[X]) * a3 * (h0 ^ 2) ^ 16 -
          (16384 : K[X]) * b5 * (h0 ^ 2) ^ 15 -
          (10240 : K[X]) * a4 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 12 +
          (12288 : K[X]) * b6 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 11 -
          (12800 : K[X]) * a5 * a6 * (h0 ^ 2) ^ 12 +
          (14336 : K[X]) * a6 * b7 * (h0 ^ 2) ^ 11 +
          (8800 : K[X]) * a5 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 8 -
          (11648 : K[X]) * b7 * (h0 ^ 4 * g1) ^ 2 * (h0 ^ 2) ^ 7 -
          (8320 : K[X]) * a6 ^ 2 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 8 +
          (6760 : K[X]) * a6 * (h0 ^ 4 * g1) ^ 3 * (h0 ^ 2) ^ 4 -
          (819 : K[X]) * (h0 ^ 4 * g1) ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * (h0 ^ 2) ^ 15 -
              (832 : K[X]) * a6 * (h0 ^ 4 * g1) * (h0 ^ 2) ^ 11 +
              (364 : K[X]) * (h0 ^ 4 * g1) ^ 3 * (h0 ^ 2) ^ 7) =
        Polynomial.C ν * h0 ^ 35 := by
    simpa only [alignedFifthDefect810, hHsq, hg] using hF
  apply mul_left_cancel₀ (pow_ne_zero 20 hh0)
  linear_combination hF'

/-- Consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `112 p₆ - 91 g₁²`, eliminates `q₇` from the
square-chamber fifth core: the cleared fifth row of the square
chamber. -/
theorem alignedSquareFifth_solved_810 {K : Type*} [Field K] [CharZero K]
    {h0 g1 a3 a4 a5 a6 b5 b6 b7 : K[X]} {κ μ ν : K}
    (hcore :
      (20480 : K[X]) * a3 * h0 ^ 12 - (16384 : K[X]) * b5 * h0 ^ 10 -
          (10240 : K[X]) * a4 * g1 * h0 ^ 8 +
          (12288 : K[X]) * b6 * g1 * h0 ^ 6 -
          (12800 : K[X]) * a5 * a6 * h0 ^ 4 +
          (14336 : K[X]) * a6 * b7 * h0 ^ 2 +
          (8800 : K[X]) * a5 * g1 ^ 2 * h0 ^ 4 -
          (11648 : K[X]) * b7 * g1 ^ 2 * h0 ^ 2 -
          (8320 : K[X]) * a6 ^ 2 * g1 + (6760 : K[X]) * a6 * g1 ^ 3 -
          (819 : K[X]) * g1 ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * h0 ^ 10 -
              (832 : K[X]) * a6 * g1 * h0 ^ 6 +
              (364 : K[X]) * g1 ^ 3 * h0 ^ 6) =
        Polynomial.C ν * h0 ^ 15)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    (20480 : K[X]) * a3 * h0 ^ 12 - (16384 : K[X]) * b5 * h0 ^ 10 -
        (10240 : K[X]) * a4 * g1 * h0 ^ 8 +
        (12288 : K[X]) * b6 * g1 * h0 ^ 6 +
        (5120 : K[X]) * a5 * a6 * h0 ^ 4 -
        (5760 : K[X]) * a5 * g1 ^ 2 * h0 ^ 4 -
        (3840 : K[X]) * a6 ^ 2 * g1 + (2560 : K[X]) * a6 * g1 ^ 3 -
        (364 : K[X]) * g1 ^ 5 +
        Polynomial.C κ *
          ((512 : K[X]) * a5 * h0 ^ 10 -
            (384 : K[X]) * a6 * g1 * h0 ^ 6) -
        Polynomial.C μ *
          ((112 : K[X]) * a6 * h0 ^ 9 -
            (91 : K[X]) * g1 ^ 2 * h0 ^ 9) =
      Polynomial.C ν * h0 ^ 15 := by
  linear_combination hcore -
    ((112 : K[X]) * a6 - (91 : K[X]) * g1 ^ 2) * hq7

/-- Factored transport form of the cleared square-chamber fifth row:
the quintic block `4 g₁ (960 p₆² - 640 p₆ g₁² + 91 g₁⁴)` is an exact
`h₀⁴`-multiple. -/
theorem alignedSquareFifth_factored_810 {K : Type*} [Field K] [CharZero K]
    {h0 g1 a3 a4 a5 a6 b5 b6 : K[X]} {κ μ ν : K}
    (hsolved :
      (20480 : K[X]) * a3 * h0 ^ 12 - (16384 : K[X]) * b5 * h0 ^ 10 -
          (10240 : K[X]) * a4 * g1 * h0 ^ 8 +
          (12288 : K[X]) * b6 * g1 * h0 ^ 6 +
          (5120 : K[X]) * a5 * a6 * h0 ^ 4 -
          (5760 : K[X]) * a5 * g1 ^ 2 * h0 ^ 4 -
          (3840 : K[X]) * a6 ^ 2 * g1 + (2560 : K[X]) * a6 * g1 ^ 3 -
          (364 : K[X]) * g1 ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * h0 ^ 10 -
              (384 : K[X]) * a6 * g1 * h0 ^ 6) -
          Polynomial.C μ *
            ((112 : K[X]) * a6 * h0 ^ 9 -
              (91 : K[X]) * g1 ^ 2 * h0 ^ 9) =
        Polynomial.C ν * h0 ^ 15) :
    (4 : K[X]) * g1 *
        ((960 : K[X]) * a6 ^ 2 - (640 : K[X]) * a6 * g1 ^ 2 +
          (91 : K[X]) * g1 ^ 4) =
      h0 ^ 4 *
        ((20480 : K[X]) * a3 * h0 ^ 8 - (16384 : K[X]) * b5 * h0 ^ 6 -
          (10240 : K[X]) * a4 * g1 * h0 ^ 4 +
          (12288 : K[X]) * b6 * g1 * h0 ^ 2 +
          (5120 : K[X]) * a5 * a6 - (5760 : K[X]) * a5 * g1 ^ 2 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * h0 ^ 6 -
              (384 : K[X]) * a6 * g1 * h0 ^ 2) -
          Polynomial.C μ *
            ((112 : K[X]) * a6 * h0 ^ 5 -
              (91 : K[X]) * g1 ^ 2 * h0 ^ 5) -
          Polynomial.C ν * h0 ^ 11) := by
  linear_combination -hsolved

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the weight-thirty-five
integral forces its constant to vanish, and with it the whole fifth
defect. -/
theorem alignedNonsquareFifth_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a3 a4 a5 a6 a7 b5 b6 b7 : k[X]} {κ κ₄ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hF2 : alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ ^ 2 =
      Polynomial.C κ₄ * H ^ 35) :
    κ₄ = 0 ∧ alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ = 0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set F : k[X] := alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ
    with hFdef
  have hdvd : (H ^ 17) ^ 2 ∣ F ^ 2 := by
    refine ⟨Polynomial.C κ₄ * H, ?_⟩
    rw [hF2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₄ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 34 hH)
    have h34 := hF2
    rw [hG] at h34
    linear_combination h34
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₄ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk4 : κ₄ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hFzero : F = 0 := by
    have hsq : F ^ 2 = 0 := by
      rw [hF2, hk4]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk4, hFzero⟩

/-- Peeling `H¹⁰` from the vanished fifth defect on `p₇ = H² g₂`, then
consuming the previous factored quotient with the mate
`112 p₆ - 91 g₂²`, leaves the cleared fifth row of the nonsquare
chamber together with its factored transport form. -/
theorem alignedNonsquareFifth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a3 a4 a5 a6 a7 b5 b6 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hF0 : alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7 κ = 0)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    (20480 : K[X]) * a3 * H ^ 6 - (16384 : K[X]) * b5 * H ^ 5 -
        (10240 : K[X]) * a4 * g2 * H ^ 4 +
        (12288 : K[X]) * b6 * g2 * H ^ 3 +
        (5120 : K[X]) * a5 * a6 * H ^ 2 -
        (5760 : K[X]) * a5 * g2 ^ 2 * H ^ 2 -
        (3840 : K[X]) * a6 ^ 2 * g2 + (2560 : K[X]) * a6 * g2 ^ 3 -
        (364 : K[X]) * g2 ^ 5 +
        Polynomial.C κ *
          ((512 : K[X]) * a5 * H ^ 5 -
            (384 : K[X]) * a6 * g2 * H ^ 3) = 0 ∧
      (4 : K[X]) * g2 *
          ((960 : K[X]) * a6 ^ 2 - (640 : K[X]) * a6 * g2 ^ 2 +
            (91 : K[X]) * g2 ^ 4) =
        H ^ 2 *
          ((20480 : K[X]) * a3 * H ^ 4 - (16384 : K[X]) * b5 * H ^ 3 -
            (10240 : K[X]) * a4 * g2 * H ^ 2 +
            (12288 : K[X]) * b6 * g2 * H +
            (5120 : K[X]) * a5 * a6 - (5760 : K[X]) * a5 * g2 ^ 2 +
            Polynomial.C κ *
              ((512 : K[X]) * a5 * H ^ 3 -
                (384 : K[X]) * a6 * g2 * H)) := by
  have hF0' :
      (20480 : K[X]) * a3 * H ^ 16 - (16384 : K[X]) * b5 * H ^ 15 -
          (10240 : K[X]) * a4 * (H ^ 2 * g2) * H ^ 12 +
          (12288 : K[X]) * b6 * (H ^ 2 * g2) * H ^ 11 -
          (12800 : K[X]) * a5 * a6 * H ^ 12 +
          (14336 : K[X]) * a6 * b7 * H ^ 11 +
          (8800 : K[X]) * a5 * (H ^ 2 * g2) ^ 2 * H ^ 8 -
          (11648 : K[X]) * b7 * (H ^ 2 * g2) ^ 2 * H ^ 7 -
          (8320 : K[X]) * a6 ^ 2 * (H ^ 2 * g2) * H ^ 8 +
          (6760 : K[X]) * a6 * (H ^ 2 * g2) ^ 3 * H ^ 4 -
          (819 : K[X]) * (H ^ 2 * g2) ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * H ^ 15 -
              (832 : K[X]) * a6 * (H ^ 2 * g2) * H ^ 11 +
              (364 : K[X]) * (H ^ 2 * g2) ^ 3 * H ^ 7) = 0 := by
    simpa only [alignedFifthDefect810, hg2] using hF0
  have hpeel :
      (20480 : K[X]) * a3 * H ^ 6 - (16384 : K[X]) * b5 * H ^ 5 -
          (10240 : K[X]) * a4 * g2 * H ^ 4 +
          (12288 : K[X]) * b6 * g2 * H ^ 3 -
          (12800 : K[X]) * a5 * a6 * H ^ 2 +
          (14336 : K[X]) * a6 * b7 * H +
          (8800 : K[X]) * a5 * g2 ^ 2 * H ^ 2 -
          (11648 : K[X]) * b7 * g2 ^ 2 * H -
          (8320 : K[X]) * a6 ^ 2 * g2 + (6760 : K[X]) * a6 * g2 ^ 3 -
          (819 : K[X]) * g2 ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * H ^ 5 -
              (832 : K[X]) * a6 * g2 * H ^ 3 +
              (364 : K[X]) * g2 ^ 3 * H ^ 3) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 10 hH)
    rw [mul_zero]
    linear_combination hF0'
  have hclear :
      (20480 : K[X]) * a3 * H ^ 6 - (16384 : K[X]) * b5 * H ^ 5 -
          (10240 : K[X]) * a4 * g2 * H ^ 4 +
          (12288 : K[X]) * b6 * g2 * H ^ 3 +
          (5120 : K[X]) * a5 * a6 * H ^ 2 -
          (5760 : K[X]) * a5 * g2 ^ 2 * H ^ 2 -
          (3840 : K[X]) * a6 ^ 2 * g2 + (2560 : K[X]) * a6 * g2 ^ 3 -
          (364 : K[X]) * g2 ^ 5 +
          Polynomial.C κ *
            ((512 : K[X]) * a5 * H ^ 5 -
              (384 : K[X]) * a6 * g2 * H ^ 3) = 0 := by
    linear_combination hpeel -
      ((112 : K[X]) * a6 - (91 : K[X]) * g2 ^ 2) * hfac
  exact ⟨hclear, by linear_combination -hclear⟩

/-! ## Source-facing fifth-row packets -/

/-- Source-facing squared weight-thirty-five integral of a normalized
aligned scale-two `(8,10)` source: the degree-`12` row is consumed into
`F² = κ₄ H³⁵` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedFifthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 35 := by
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
  exact ⟨κ, κ₃, κ₄, aligned_q9_solved_810 haligned, hM, hE4, hF2⟩

/-- Exact square-chamber fifth packet of a normalized aligned scale-two
`(8,10)` source: on top of `p₇ = h₀⁴ g₁`, `q₉ = (5/4) g₁ h₀⁶`, and the
previous packet, the consumed degree-`12` row gives the polynomial
square root `F = ν h₀³⁵` with `ν² = κ₄`, the cleared fifth row, its
factored transport form, the carried root collapse `g₁ = p₆ = 0`, and
the carried descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedFifthFace_squareChamber_packet
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
    ∃ (κ μ κ₄ ν : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ν ^ 2 = κ₄ ∧
        (20480 : K[X]) * p.coeff 3 * h0 ^ 12 -
            (16384 : K[X]) * q.coeff 5 * h0 ^ 10 -
            (10240 : K[X]) * p.coeff 4 * g1 * h0 ^ 8 +
            (12288 : K[X]) * q.coeff 6 * g1 * h0 ^ 6 +
            (5120 : K[X]) * p.coeff 5 * p.coeff 6 * h0 ^ 4 -
            (5760 : K[X]) * p.coeff 5 * g1 ^ 2 * h0 ^ 4 -
            (3840 : K[X]) * p.coeff 6 ^ 2 * g1 +
            (2560 : K[X]) * p.coeff 6 * g1 ^ 3 -
            (364 : K[X]) * g1 ^ 5 +
            Polynomial.C κ *
              ((512 : K[X]) * p.coeff 5 * h0 ^ 10 -
                (384 : K[X]) * p.coeff 6 * g1 * h0 ^ 6) -
            Polynomial.C μ *
              ((112 : K[X]) * p.coeff 6 * h0 ^ 9 -
                (91 : K[X]) * g1 ^ 2 * h0 ^ 9) =
          Polynomial.C ν * h0 ^ 15 ∧
        (4 : K[X]) * g1 *
            ((960 : K[X]) * p.coeff 6 ^ 2 -
              (640 : K[X]) * p.coeff 6 * g1 ^ 2 +
              (91 : K[X]) * g1 ^ 4) =
          h0 ^ 4 *
            ((20480 : K[X]) * p.coeff 3 * h0 ^ 8 -
              (16384 : K[X]) * q.coeff 5 * h0 ^ 6 -
              (10240 : K[X]) * p.coeff 4 * g1 * h0 ^ 4 +
              (12288 : K[X]) * q.coeff 6 * g1 * h0 ^ 2 +
              (5120 : K[X]) * p.coeff 5 * p.coeff 6 -
              (5760 : K[X]) * p.coeff 5 * g1 ^ 2 +
              Polynomial.C κ *
                ((512 : K[X]) * p.coeff 5 * h0 ^ 6 -
                  (384 : K[X]) * p.coeff 6 * g1 * h0 ^ 2) -
              Polynomial.C μ *
                ((112 : K[X]) * p.coeff 6 * h0 ^ 5 -
                  (91 : K[X]) * g1 ^ 2 * h0 ^ 5) -
              Polynomial.C ν * h0 ^ 11) ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C ν * h0 ^ 35 := by
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
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨ν, hν2, hF⟩ := alignedSquareFifth_sqrt_810 hh0 hHsq hF2
  have hcore5 := alignedSquareFifth_core_810 hh0 hHsq hp7 hF
  have hsolved5 := alignedSquareFifth_solved_810 hcore5 hcore
  have hfact5 := alignedSquareFifth_factored_810 hsolved5
  exact ⟨κ, μ, κ₄, ν, g1, hp7, by rw [hq9, hg, hg1, hHsq]; ring, hν2,
    hsolved5, hfact5, hcollapse, hdvdg1, hdvdp6, hF⟩

/-- Exact nonsquare-chamber fifth packet of a normalized aligned
scale-two `(8,10)` source: the weight-thirty-five constant vanishes,
the fifth defect is identically zero, and on top of `p₇ = H² g₂` and
the previous packet the consumed degree-`12` row gives the cleared
fifth row, its factored transport form, the carried root collapse
`g₂ = p₆ = 0` at every (simple) root of the core, and the carried
descents `H ∣ g₂`, `H ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedFifthFace_nonsquareChamber_packet
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
        (20480 : K[X]) * p.coeff 3 * H ^ 6 -
            (16384 : K[X]) * q.coeff 5 * H ^ 5 -
            (10240 : K[X]) * p.coeff 4 * g2 * H ^ 4 +
            (12288 : K[X]) * q.coeff 6 * g2 * H ^ 3 +
            (5120 : K[X]) * p.coeff 5 * p.coeff 6 * H ^ 2 -
            (5760 : K[X]) * p.coeff 5 * g2 ^ 2 * H ^ 2 -
            (3840 : K[X]) * p.coeff 6 ^ 2 * g2 +
            (2560 : K[X]) * p.coeff 6 * g2 ^ 3 -
            (364 : K[X]) * g2 ^ 5 +
            Polynomial.C κ *
              ((512 : K[X]) * p.coeff 5 * H ^ 5 -
                (384 : K[X]) * p.coeff 6 * g2 * H ^ 3) = 0 ∧
        (4 : K[X]) * g2 *
            ((960 : K[X]) * p.coeff 6 ^ 2 -
              (640 : K[X]) * p.coeff 6 * g2 ^ 2 +
              (91 : K[X]) * g2 ^ 4) =
          H ^ 2 *
            ((20480 : K[X]) * p.coeff 3 * H ^ 4 -
              (16384 : K[X]) * q.coeff 5 * H ^ 3 -
              (10240 : K[X]) * p.coeff 4 * g2 * H ^ 2 +
              (12288 : K[X]) * q.coeff 6 * g2 * H +
              (5120 : K[X]) * p.coeff 5 * p.coeff 6 -
              (5760 : K[X]) * p.coeff 5 * g2 ^ 2 +
              Polynomial.C κ *
                ((512 : K[X]) * p.coeff 5 * H ^ 3 -
                  (384 : K[X]) * p.coeff 6 * g2 * H)) ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
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
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk4, hF0⟩ :=
    alignedNonsquareFifth_defect_eq_zero_810 hH hHdegree hnsq hF2
  obtain ⟨hclear5, hfact5⟩ :=
    alignedNonsquareFifth_solved_810 hH hg2 hF0 hfac
  exact ⟨κ, g2, hg2, by rw [hq9, hg2]; ring, hclear5, hfact5,
    hcollapse, hdvdg2, hdvdp6, hF0⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`12`
aligned row.  Neither chamber is excluded, the constants `κ`, `μ`,
`κ₄ = ν²` are preserved where not forced, and no closure is
claimed. -/
theorem normalized810ScaleTwo_alignedFifthFace_chamberDichotomy
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
      ∃ (κ μ ν : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (4 : K[X]) * g1 *
              ((960 : K[X]) * p.coeff 6 ^ 2 -
                (640 : K[X]) * p.coeff 6 * g1 ^ 2 +
                (91 : K[X]) * g1 ^ 4) =
            h0 ^ 4 *
              ((20480 : K[X]) * p.coeff 3 * h0 ^ 8 -
                (16384 : K[X]) * q.coeff 5 * h0 ^ 6 -
                (10240 : K[X]) * p.coeff 4 * g1 * h0 ^ 4 +
                (12288 : K[X]) * q.coeff 6 * g1 * h0 ^ 2 +
                (5120 : K[X]) * p.coeff 5 * p.coeff 6 -
                (5760 : K[X]) * p.coeff 5 * g1 ^ 2 +
                Polynomial.C κ *
                  ((512 : K[X]) * p.coeff 5 * h0 ^ 6 -
                    (384 : K[X]) * p.coeff 6 * g1 * h0 ^ 2) -
                Polynomial.C μ *
                  ((112 : K[X]) * p.coeff 6 * h0 ^ 5 -
                    (91 : K[X]) * g1 ^ 2 * h0 ^ 5) -
                Polynomial.C ν * h0 ^ 11) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (4 : K[X]) * g2 *
              ((960 : K[X]) * p.coeff 6 ^ 2 -
                (640 : K[X]) * p.coeff 6 * g2 ^ 2 +
                (91 : K[X]) * g2 ^ 4) =
            H ^ 2 *
              ((20480 : K[X]) * p.coeff 3 * H ^ 4 -
                (16384 : K[X]) * q.coeff 5 * H ^ 3 -
                (10240 : K[X]) * p.coeff 4 * g2 * H ^ 2 +
                (12288 : K[X]) * q.coeff 6 * g2 * H +
                (5120 : K[X]) * p.coeff 5 * p.coeff 6 -
                (5760 : K[X]) * p.coeff 5 * g2 ^ 2 +
                Polynomial.C κ *
                  ((512 : K[X]) * p.coeff 5 * H ^ 3 -
                    (384 : K[X]) * p.coeff 6 * g2 * H)) ∧
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
      normalized810ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, _κ₄, ν, g1, hp7, hq9, _hν2, _hsolved, hfact,
      hcollapse, hdvdg1, hdvdp6, _hF⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, ν, g1, hp7, hq9, hfact,
      hcollapse, hdvdg1, hdvdp6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, _hclear, hfact, hcollapse,
      hdvdg2, hdvdp6, _hF0⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g2, hp7, hq9, hfact,
      hcollapse, hdvdg2, hdvdp6⟩

/-- Chamber-independent root jet after the consumed degree-`12` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its quintic content is absorbed by the
previous collapse (`alignedFifth_rootQuintic_absorbed_810`) — and the
new coefficients `p₃, q₅` are tied into the cleared fifth row instead
of being killed. -/
theorem normalized810ScaleTwo_alignedFifthFace_rootJet
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
  normalized810ScaleTwo_alignedFourthFace_rootJet hsource haligned

#print axioms alignedFifthCoefficientJacobianRow_810
#print axioms alignedFifthDefect_weightedDerivative_identity_810
#print axioms alignedFifthDefectRow_eq_zero_810
#print axioms alignedFifthDefectPowerRelation_810
#print axioms alignedFifth_factored_rootBranch_810
#print axioms alignedFifth_rootQuintic_absorbed_810
#print axioms alignedSquareFifth_sqrt_810
#print axioms alignedSquareFifth_core_810
#print axioms alignedSquareFifth_solved_810
#print axioms alignedSquareFifth_factored_810
#print axioms alignedNonsquareFifth_defect_eq_zero_810
#print axioms alignedNonsquareFifth_solved_810
#print axioms normalized810ScaleTwo_alignedFifthFace_packet
#print axioms normalized810ScaleTwo_alignedFifthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedFifthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedFifthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedFifthFace_rootJet

end Max11DegreeRoutes
