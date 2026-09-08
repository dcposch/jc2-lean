import Fable810ScaleTwoAlignedFifthFaceScratch

/-! # Sixth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedFifthFaceScratch` consumed the degree-`11`
aligned Keller row (the chamber-free `G = κ₅ H²¹`).  This file consumes
the next unused aligned row, the degree-`10` Jacobian coefficient — the
first row that sees `p₁` and `q₃` (internal names `alignedSeventh*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, `H G' - 21 G H' = 0`,
the degree-`10` row is the weighted derivative of the weight-forty-nine
defect

`I = 5242880 p₁ H²⁴ - 4194304 q₃ H²³ - 1310720 p₂ p₇ H²⁰
  + 2097152 q₄ p₇ H¹⁹ - 1966080 p₃ p₆ H²⁰ + 2621440 q₅ p₆ H¹⁹
  + 1105920 p₃ p₇² H¹⁶ - 1802240 q₅ p₇² H¹⁵ - 7208960 p₄ p₅ H²⁰
  + 3670016 p₄ q₇ H¹⁹ + 3145728 p₅ q₆ H¹⁹ + 1802240 p₄ p₆ p₇ H¹⁶
  - 4325376 q₆ p₆ p₇ H¹⁵ - 901120 p₄ p₇³ H¹² + 1712128 q₆ p₇³ H¹¹
  + 4505600 p₅² p₇ H¹⁶ - 5046272 p₅ q₇ p₇ H¹⁵ + 1351680 p₅ p₆² H¹⁶
  - 2523136 q₇ p₆² H¹⁵ - 1971200 p₅ p₆ p₇² H¹² + 5992448 q₇ p₆ p₇² H¹¹
  + 769120 p₅ p₇⁴ H⁸ - 1685376 q₇ p₇⁴ H⁷ + 2140160 p₆³ p₇ H¹²
  - 3745280 p₆² p₇³ H⁸ + 1429560 p₆ p₇⁵ H⁴ - 141075 p₇⁷
  + κ (131072 p₃ H²³ - 180224 p₄ p₇ H¹⁹ - 180224 p₅ p₆ H¹⁹
       + 214016 p₅ p₇² H¹⁵ + 214016 p₆² p₇ H¹⁵ - 240768 p₆ p₇³ H¹¹
       + 52668 p₇⁵ H⁷)`,

via the exact multiplier identity

`1048576 H²⁰ H⁴ · row₁₀[p₈ = H⁴, q₁₀ = H⁵] = (2 H I' - 49 I H')
  - 2359296 H²⁰ p₂' N + 524288 H²⁰ p₂ N'
  + (262144 H¹⁷ p₃' + 294912 p₃ H¹⁶ H') C - 98304 H¹⁷ p₃ C'
  + (45056 p₄ H¹² + 39424 p₅ p₇ H⁸ + 19712 p₆² H⁸ - 2464 p₆ p₇² H⁴
     + 231 p₇⁴) (2 H D' - 21 D H')
  + (5632 p₅ H⁸ + 4224 p₆ p₇ H⁴ - 176 p₇³) (H E' - 14 E H')
  + (352 p₆ H⁴ + 110 p₇²) (2 H F' - 35 F H')
  + 176 p₇ (H G' - 21 G H')`.

On the aligned face every right-hand correction vanishes, so
`2 H I' = 49 I H'` and the squared weight-forty-nine first integral

`I² = κ₆ H⁴⁹`

holds for a preserved constant `κ₆`.  The exponent is odd, so — exactly
as for the degree-`14` and degree-`12` rows — the integral is
**chambered**:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: `I = ν₂ h₀⁴⁹` with
  `ν₂² = κ₆`; peeling `h₀²⁸` and consuming the previous factored
  quotient (`128 q₇ h₀²` solved, transported by the mate
  `28672 p₄ h₀⁸ - 39424 p₅ g₁ h₀⁴ - 19712 p₆² + 46816 p₆ g₁²
   - 13167 g₁⁴`) leaves the cleared seventh row with `p₁` at `h₀²⁰` and
  `q₃` at `h₀¹⁸` against `ν₂ h₀²¹`, and the factored transport
  `440 g₁ (171 g₁⁶ - 1520 p₆ g₁⁴ + 4032 p₆² g₁² - 3072 p₆³)
   = h₀⁴ · (co-factor)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₆ = 0` and `I ≡ 0`.  With `p₇ = H² g₂`, peeling
  `H¹⁴` and consuming the previous factored quotient (same mate) leaves
  the cleared seventh row (with `p₁` at `H¹⁰` and `q₃` at `H⁹`) equal
  to zero and the transport
  `440 g₂ (171 g₂⁶ - 1520 p₆ g₂⁴ + 4032 p₆² g₂² - 3072 p₆³)
   = H² · (co-factor)`.

At a root of the core the transport leaves the honest root branch
`g = 0 ∨ 171 g⁶ - 1520 p₆ g⁴ + 4032 p₆² g² - 3072 p₆³ = 0`.  Like the
quintic and sextic of the previous rows it adds *no new* root
information: the consumed degree-`13` row already collapsed
`g(a) = 0 ∧ p₆(a) = 0` at every core root, and that collapse absorbs
the septic identically (`alignedSeventh_rootSeptic_absorbed_810`).  The
chamber-independent root jet therefore stays `p₇, q₉, q₈, p₆` — the row
ties the new coefficients `p₁, q₃` into the cleared seventh row
(at `h₀²⁰`/`h₀¹⁸`, resp. `H¹⁰`/`H⁹`) instead of killing anything new at
the root.

No closure is claimed.  Both chambers remain open, the constants `κ`,
`μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆ = ν₂²` are preserved where not forced, the
zero branches (`g₁ = 0`, `g₂ = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`,
`κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`) are not excluded as polynomial
identities, the deepened quotients `g₁/h₀`, `p₆/h₀`, `g₂/H`, `p₆/H`
from the degree-`13` face are still not re-cleared through the tower
here, the root septic is recorded but not excluded as an identity, and
no individual vanishing of `p₁`, `p₂`, `p₃`, `p₄`, `p₅`, `q₃`, `q₄`,
`q₅`, `q₆`, `q₇` is claimed.  The next unused Keller row on the aligned
face is the degree-`9` Jacobian coefficient, the first row that sees
`p₀` and `q₂` (weight-fifty-six defect, even exponent, hence
chamber-free).  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`10` Keller coefficient on the aligned face -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`10` Jacobian coefficient, the first
aligned row that sees `p₁` and `q₃`. -/
theorem alignedSeventhCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 7).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 3).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 4).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 9).derivative +
        p.coeff 1 * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 10) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (10 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 10 :
      Finset (ℕ × ℕ)) =
      ({(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4),
        (7, 3), (8, 2), (9, 1),
        (10, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC2]
  linear_combination hcoeff

/-! ## Aligned seventh defect -/

/-- Weight-forty-nine defect of the degree-`10` aligned `(8,10)` row.
On the aligned face its square is a polynomial first integral of odd
weight forty-nine, hence chambered. -/
def alignedSeventhDefect810 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 : K[X]) (κ : K) : K[X] :=
  (5242880 : K[X]) * a1 * H ^ 24 - (4194304 : K[X]) * b3 * H ^ 23 -
    (1310720 : K[X]) * a2 * a7 * H ^ 20 +
    (2097152 : K[X]) * b4 * a7 * H ^ 19 -
    (1966080 : K[X]) * a3 * a6 * H ^ 20 +
    (2621440 : K[X]) * b5 * a6 * H ^ 19 +
    (1105920 : K[X]) * a3 * a7 ^ 2 * H ^ 16 -
    (1802240 : K[X]) * b5 * a7 ^ 2 * H ^ 15 -
    (7208960 : K[X]) * a4 * a5 * H ^ 20 +
    (3670016 : K[X]) * a4 * b7 * H ^ 19 +
    (3145728 : K[X]) * a5 * b6 * H ^ 19 +
    (1802240 : K[X]) * a4 * a6 * a7 * H ^ 16 -
    (4325376 : K[X]) * b6 * a6 * a7 * H ^ 15 -
    (901120 : K[X]) * a4 * a7 ^ 3 * H ^ 12 +
    (1712128 : K[X]) * b6 * a7 ^ 3 * H ^ 11 +
    (4505600 : K[X]) * a5 ^ 2 * a7 * H ^ 16 -
    (5046272 : K[X]) * a5 * b7 * a7 * H ^ 15 +
    (1351680 : K[X]) * a5 * a6 ^ 2 * H ^ 16 -
    (2523136 : K[X]) * b7 * a6 ^ 2 * H ^ 15 -
    (1971200 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 12 +
    (5992448 : K[X]) * b7 * a6 * a7 ^ 2 * H ^ 11 +
    (769120 : K[X]) * a5 * a7 ^ 4 * H ^ 8 -
    (1685376 : K[X]) * b7 * a7 ^ 4 * H ^ 7 +
    (2140160 : K[X]) * a6 ^ 3 * a7 * H ^ 12 -
    (3745280 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 8 +
    (1429560 : K[X]) * a6 * a7 ^ 5 * H ^ 4 - (141075 : K[X]) * a7 ^ 7 +
    Polynomial.C κ *
      ((131072 : K[X]) * a3 * H ^ 23 - (180224 : K[X]) * a4 * a7 * H ^ 19 -
        (180224 : K[X]) * a5 * a6 * H ^ 19 +
        (214016 : K[X]) * a5 * a7 ^ 2 * H ^ 15 +
        (214016 : K[X]) * a6 ^ 2 * a7 * H ^ 15 -
        (240768 : K[X]) * a6 * a7 ^ 3 * H ^ 11 +
        (52668 : K[X]) * a7 ^ 5 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`10` Jacobian expression with the
weighted derivative of `I`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, degree-`12`, and degree-`11` rows. -/
theorem alignedSeventhDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 b8 b9 : K[X]) (κ : K) :
    (1048576 : K[X]) * H ^ 20 *
        ((H ^ 4).derivative * (b3 * (3 : K[X])) +
          a7.derivative * (b4 * (4 : K[X])) +
          a6.derivative * (b5 * (5 : K[X])) +
          a5.derivative * (b6 * (6 : K[X])) +
          a4.derivative * (b7 * (7 : K[X])) +
          a3.derivative * (b8 * (8 : K[X])) +
          a2.derivative * (b9 * (9 : K[X])) +
          a1.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b3.derivative +
          (a7 * (7 : K[X])) * b4.derivative +
          (a6 * (6 : K[X])) * b5.derivative +
          (a5 * (5 : K[X])) * b6.derivative +
          (a4 * (4 : K[X])) * b7.derivative +
          (a3 * (3 : K[X])) * b8.derivative +
          (a2 * (2 : K[X])) * b9.derivative +
          a1 * (H ^ 5).derivative)) =
      ((2 : K[X]) * H *
          (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
            κ).derivative -
        (49 : K[X]) *
          alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
            κ * H.derivative) -
        (2359296 : K[X]) * H ^ 20 * a2.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        (524288 : K[X]) * H ^ 20 * a2 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative +
        ((262144 : K[X]) * H ^ 17 * a3.derivative +
            (294912 : K[X]) * a3 * H ^ 16 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (98304 : K[X]) * H ^ 17 * a3 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((45056 : K[X]) * a4 * H ^ 12 + (39424 : K[X]) * a5 * a7 * H ^ 8 +
            (19712 : K[X]) * a6 ^ 2 * H ^ 8 -
            (2464 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (231 : K[X]) * a7 ^ 4) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((5632 : K[X]) * a5 * H ^ 8 + (4224 : K[X]) * a6 * a7 * H ^ 4 -
            (176 : K[X]) * a7 ^ 3) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((352 : K[X]) * a6 * H ^ 4 + (110 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        (176 : K[X]) * a7 *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) := by
  simp only [alignedSeventhDefect810, alignedSixthDefect810,
    alignedFifthDefect810, alignedFourthDefect810, alignedThirdDefect810,
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
degree-`13`, degree-`12`, and degree-`11` rows, the degree-`10` row is
the weighted derivative `2 H I' - 49 I H' = 0`. -/
theorem alignedSeventhDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (49 : K[X]) *
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
        H.derivative = 0 := by
  have hrow := alignedSeventhCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC2] at hrow
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
  have hrowG :
      H * (alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (21 : K[X]) *
          alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedSixthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hid := alignedSeventhDefect_weightedDerivative_identity_810
    H (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
    (p.coeff 6) (p.coeff 7) (q.coeff 3) (q.coeff 4) (q.coeff 5)
    (q.coeff 6) (q.coeff 7) (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD, hrowE, hrowF, hrowG] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-forty-nine polynomial first integral of the aligned
`(8,10)` seventh defect: `I² = κ₆ H⁴⁹`.  The exponent is odd, so the
integral is chambered. -/
theorem alignedSeventhDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₆ : K,
      alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
          (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₆ * H ^ 49 := by
  let I : K[X] :=
    alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * I.derivative -
        (49 : K[X]) * I * H.derivative = 0 := by
    simpa only [I] using
      alignedSeventhDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC49 : Polynomial.C (49 : K) = (49 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (I ^ 2) (H ^ 49) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      I ^ 2 * (Polynomial.C (49 : K) * H ^ (49 - 1) * H.derivative) -
          Polynomial.C (2 : K) * I ^ (2 - 1) * I.derivative * H ^ 49 =
          I * H ^ 48 *
            (Polynomial.C (49 : K) * I * H.derivative -
              Polynomial.C (2 : K) * H * I.derivative) := by
        ring
      _ = 0 := by
        rw [hC49, hC2]
        have hfac :
            (49 : K[X]) * I * H.derivative -
              (2 : K[X]) * H * I.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 49 hH) hW

/-! ## Root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport seventh row at a root of its
cofactor: either the descent quotient vanishes there, or the septic
core `171 g⁶ - 1520 p₆ g⁴ + 4032 p₆² g² - 3072 p₆³` does.  Neither
branch is excluded. -/
theorem alignedSeventh_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (440 : K[X]) * g *
        ((171 : K[X]) * g ^ 6 - (1520 : K[X]) * a6 * g ^ 4 +
          (4032 : K[X]) * a6 ^ 2 * g ^ 2 - (3072 : K[X]) * a6 ^ 3) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨
      171 * (g.eval a) ^ 6 - 1520 * a6.eval a * (g.eval a) ^ 4 +
        4032 * (a6.eval a) ^ 2 * (g.eval a) ^ 2 -
        3072 * (a6.eval a) ^ 3 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h440g | hsept
  · exact Or.inl
      ((mul_eq_zero.mp h440g).resolve_left (by norm_num : (440 : K) ≠ 0))
  · exact Or.inr (by linear_combination hsept)

/-- The root septic of the consumed degree-`10` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the seventh row adds no new root
constraint. -/
theorem alignedSeventh_rootSeptic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    440 * G * (171 * G ^ 6 - 1520 * P6 * G ^ 4 + 4032 * P6 ^ 2 * G ^ 2 -
      3072 * P6 ^ 3) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Square chamber -/

/-- In the square chamber the squared weight-forty-nine integral has a
polynomial square root with square core: `I = ν₂ h₀⁴⁹` with `ν₂² = κ₆`.
The constant `ν₂` is preserved, not cleared. -/
theorem alignedSquareSeventh_sqrt_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 : K[X]} {κ κ₆ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hI2 : alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
        κ ^ 2 =
      Polynomial.C κ₆ * H ^ 49) :
    ∃ ν₂ : K, ν₂ ^ 2 = κ₆ ∧
      alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 κ =
        Polynomial.C ν₂ * h0 ^ 49 := by
  set I : K[X] :=
    alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 κ
    with hIdef
  have hdvd : (h0 ^ 49) ^ 2 ∣ I ^ 2 := by
    refine ⟨Polynomial.C κ₆, ?_⟩
    rw [hI2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₆ := by
    have h98 := hI2
    rw [hG, hHsq] at h98
    apply mul_left_cancel₀ (pow_ne_zero 98 hh0)
    linear_combination h98
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₆
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν₂, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν₂, ?_, ?_⟩
  · have hCν : Polynomial.C (ν₂ ^ 2) = Polynomial.C κ₆ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀²⁸` from `I = ν₂ h₀⁴⁹` on `p₇ = h₀⁴ g₁` and consuming
the previous factored quotient (`128 q₇ h₀²` solved), transported by
the mate `28672 p₄ h₀⁸ - 39424 p₅ g₁ h₀⁴ - 19712 p₆² + 46816 p₆ g₁²
- 13167 g₁⁴`, leaves the cleared seventh row of the square chamber
together with its factored transport form. -/
theorem alignedSquareSeventh_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 : K[X]} {κ μ ν₂ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hI : alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
        κ =
      Polynomial.C ν₂ * h0 ^ 49)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    (5242880 : K[X]) * a1 * h0 ^ 20 - (4194304 : K[X]) * b3 * h0 ^ 18 -
        (1310720 : K[X]) * a2 * g1 * h0 ^ 16 +
        (2097152 : K[X]) * b4 * g1 * h0 ^ 14 +
        (1105920 : K[X]) * a3 * g1 ^ 2 * h0 ^ 12 -
        (1966080 : K[X]) * a3 * a6 * h0 ^ 12 -
        (2621440 : K[X]) * a4 * a5 * h0 ^ 12 -
        (1802240 : K[X]) * b5 * g1 ^ 2 * h0 ^ 10 +
        (2621440 : K[X]) * b5 * a6 * h0 ^ 10 +
        (3145728 : K[X]) * a5 * b6 * h0 ^ 10 -
        (1044480 : K[X]) * a4 * g1 ^ 3 * h0 ^ 8 +
        (2949120 : K[X]) * a4 * a6 * g1 * h0 ^ 8 -
        (1802240 : K[X]) * a5 ^ 2 * g1 * h0 ^ 8 +
        (1712128 : K[X]) * b6 * g1 ^ 3 * h0 ^ 6 -
        (4325376 : K[X]) * b6 * a6 * g1 * h0 ^ 6 -
        (1140480 : K[X]) * a5 * g1 ^ 4 * h0 ^ 4 +
        (3942400 : K[X]) * a5 * a6 * g1 ^ 2 * h0 ^ 4 -
        (1802240 : K[X]) * a5 * a6 ^ 2 * h0 ^ 4 +
        (1351680 : K[X]) * a6 ^ 3 * g1 -
        (1774080 : K[X]) * a6 ^ 2 * g1 ^ 3 +
        (668800 : K[X]) * a6 * g1 ^ 5 - (75240 : K[X]) * g1 ^ 7 +
        Polynomial.C κ *
          ((131072 : K[X]) * a3 * h0 ^ 18 -
            (65536 : K[X]) * a4 * g1 * h0 ^ 14 +
            (56320 : K[X]) * a5 * g1 ^ 2 * h0 ^ 10 -
            (180224 : K[X]) * a5 * a6 * h0 ^ 10 -
            (53504 : K[X]) * a6 * g1 ^ 3 * h0 ^ 6 +
            (135168 : K[X]) * a6 ^ 2 * g1 * h0 ^ 6) -
        Polynomial.C μ *
          ((28672 : K[X]) * a4 * h0 ^ 17 -
            (39424 : K[X]) * a5 * g1 * h0 ^ 13 -
            (19712 : K[X]) * a6 ^ 2 * h0 ^ 9 +
            (46816 : K[X]) * a6 * g1 ^ 2 * h0 ^ 9 -
            (13167 : K[X]) * g1 ^ 4 * h0 ^ 9) =
      Polynomial.C ν₂ * h0 ^ 21 ∧
    (440 : K[X]) * g1 *
        ((171 : K[X]) * g1 ^ 6 - (1520 : K[X]) * a6 * g1 ^ 4 +
          (4032 : K[X]) * a6 ^ 2 * g1 ^ 2 - (3072 : K[X]) * a6 ^ 3) =
      h0 ^ 4 *
        ((5242880 : K[X]) * a1 * h0 ^ 16 -
          (4194304 : K[X]) * b3 * h0 ^ 14 -
          (1310720 : K[X]) * a2 * g1 * h0 ^ 12 +
          (2097152 : K[X]) * b4 * g1 * h0 ^ 10 +
          (1105920 : K[X]) * a3 * g1 ^ 2 * h0 ^ 8 -
          (1966080 : K[X]) * a3 * a6 * h0 ^ 8 -
          (2621440 : K[X]) * a4 * a5 * h0 ^ 8 -
          (1802240 : K[X]) * b5 * g1 ^ 2 * h0 ^ 6 +
          (2621440 : K[X]) * b5 * a6 * h0 ^ 6 +
          (3145728 : K[X]) * a5 * b6 * h0 ^ 6 -
          (1044480 : K[X]) * a4 * g1 ^ 3 * h0 ^ 4 +
          (2949120 : K[X]) * a4 * a6 * g1 * h0 ^ 4 -
          (1802240 : K[X]) * a5 ^ 2 * g1 * h0 ^ 4 +
          (1712128 : K[X]) * b6 * g1 ^ 3 * h0 ^ 2 -
          (4325376 : K[X]) * b6 * a6 * g1 * h0 ^ 2 -
          (1140480 : K[X]) * a5 * g1 ^ 4 +
          (3942400 : K[X]) * a5 * a6 * g1 ^ 2 -
          (1802240 : K[X]) * a5 * a6 ^ 2 +
          Polynomial.C κ *
            ((131072 : K[X]) * a3 * h0 ^ 14 -
              (65536 : K[X]) * a4 * g1 * h0 ^ 10 +
              (56320 : K[X]) * a5 * g1 ^ 2 * h0 ^ 6 -
              (180224 : K[X]) * a5 * a6 * h0 ^ 6 -
              (53504 : K[X]) * a6 * g1 ^ 3 * h0 ^ 2 +
              (135168 : K[X]) * a6 ^ 2 * g1 * h0 ^ 2) -
          Polynomial.C μ *
            ((28672 : K[X]) * a4 * h0 ^ 13 -
              (39424 : K[X]) * a5 * g1 * h0 ^ 9 -
              (19712 : K[X]) * a6 ^ 2 * h0 ^ 5 +
              (46816 : K[X]) * a6 * g1 ^ 2 * h0 ^ 5 -
              (13167 : K[X]) * g1 ^ 4 * h0 ^ 5) -
          Polynomial.C ν₂ * h0 ^ 17) := by
  have hI' := hI
  simp only [alignedSeventhDefect810, hHsq, hg] at hI'
  have hclear :
      (5242880 : K[X]) * a1 * h0 ^ 20 - (4194304 : K[X]) * b3 * h0 ^ 18 -
          (1310720 : K[X]) * a2 * g1 * h0 ^ 16 +
          (2097152 : K[X]) * b4 * g1 * h0 ^ 14 +
          (1105920 : K[X]) * a3 * g1 ^ 2 * h0 ^ 12 -
          (1966080 : K[X]) * a3 * a6 * h0 ^ 12 -
          (2621440 : K[X]) * a4 * a5 * h0 ^ 12 -
          (1802240 : K[X]) * b5 * g1 ^ 2 * h0 ^ 10 +
          (2621440 : K[X]) * b5 * a6 * h0 ^ 10 +
          (3145728 : K[X]) * a5 * b6 * h0 ^ 10 -
          (1044480 : K[X]) * a4 * g1 ^ 3 * h0 ^ 8 +
          (2949120 : K[X]) * a4 * a6 * g1 * h0 ^ 8 -
          (1802240 : K[X]) * a5 ^ 2 * g1 * h0 ^ 8 +
          (1712128 : K[X]) * b6 * g1 ^ 3 * h0 ^ 6 -
          (4325376 : K[X]) * b6 * a6 * g1 * h0 ^ 6 -
          (1140480 : K[X]) * a5 * g1 ^ 4 * h0 ^ 4 +
          (3942400 : K[X]) * a5 * a6 * g1 ^ 2 * h0 ^ 4 -
          (1802240 : K[X]) * a5 * a6 ^ 2 * h0 ^ 4 +
          (1351680 : K[X]) * a6 ^ 3 * g1 -
          (1774080 : K[X]) * a6 ^ 2 * g1 ^ 3 +
          (668800 : K[X]) * a6 * g1 ^ 5 - (75240 : K[X]) * g1 ^ 7 +
          Polynomial.C κ *
            ((131072 : K[X]) * a3 * h0 ^ 18 -
              (65536 : K[X]) * a4 * g1 * h0 ^ 14 +
              (56320 : K[X]) * a5 * g1 ^ 2 * h0 ^ 10 -
              (180224 : K[X]) * a5 * a6 * h0 ^ 10 -
              (53504 : K[X]) * a6 * g1 ^ 3 * h0 ^ 6 +
              (135168 : K[X]) * a6 ^ 2 * g1 * h0 ^ 6) -
          Polynomial.C μ *
            ((28672 : K[X]) * a4 * h0 ^ 17 -
              (39424 : K[X]) * a5 * g1 * h0 ^ 13 -
              (19712 : K[X]) * a6 ^ 2 * h0 ^ 9 +
              (46816 : K[X]) * a6 * g1 ^ 2 * h0 ^ 9 -
              (13167 : K[X]) * g1 ^ 4 * h0 ^ 9) =
        Polynomial.C ν₂ * h0 ^ 21 := by
    apply mul_left_cancel₀ (pow_ne_zero 28 hh0)
    linear_combination hI' -
      h0 ^ 28 *
        ((28672 : K[X]) * a4 * h0 ^ 8 - (39424 : K[X]) * a5 * g1 * h0 ^ 4 -
          (19712 : K[X]) * a6 ^ 2 + (46816 : K[X]) * a6 * g1 ^ 2 -
          (13167 : K[X]) * g1 ^ 4) * hq7
  exact ⟨hclear, by linear_combination -hclear⟩

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the squared
weight-forty-nine integral forces its constant to vanish, and with it
the whole seventh defect. -/
theorem alignedNonsquareSeventh_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 : k[X]} {κ κ₆ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hI2 : alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
        κ ^ 2 =
      Polynomial.C κ₆ * H ^ 49) :
    κ₆ = 0 ∧
      alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set I : k[X] :=
    alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 κ
    with hIdef
  have hdvd : (H ^ 24) ^ 2 ∣ I ^ 2 := by
    refine ⟨Polynomial.C κ₆ * H, ?_⟩
    rw [hI2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₆ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 48 hH)
    have h48 := hI2
    rw [hG] at h48
    linear_combination h48
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₆ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk6 : κ₆ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hIzero : I = 0 := by
    have hsq : I ^ 2 = 0 := by
      rw [hI2, hk6]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk6, hIzero⟩

set_option maxHeartbeats 1600000000 in
/-- Peeling `H¹⁴` from the vanished seventh defect on `p₇ = H² g₂`,
then consuming the previous factored quotient with the mate
`28672 p₄ H⁴ - 39424 p₅ g₂ H² - 19712 p₆² + 46816 p₆ g₂²
- 13167 g₂⁴`, leaves the cleared seventh row of the nonsquare chamber
together with its factored transport form. -/
theorem alignedNonsquareSeventh_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hI0 : alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5 b6 b7
        κ = 0)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    (5242880 : K[X]) * a1 * H ^ 10 - (4194304 : K[X]) * b3 * H ^ 9 -
        (1310720 : K[X]) * a2 * g2 * H ^ 8 +
        (2097152 : K[X]) * b4 * g2 * H ^ 7 +
        (1105920 : K[X]) * a3 * g2 ^ 2 * H ^ 6 -
        (1966080 : K[X]) * a3 * a6 * H ^ 6 -
        (2621440 : K[X]) * a4 * a5 * H ^ 6 -
        (1802240 : K[X]) * b5 * g2 ^ 2 * H ^ 5 +
        (2621440 : K[X]) * b5 * a6 * H ^ 5 +
        (3145728 : K[X]) * a5 * b6 * H ^ 5 -
        (1044480 : K[X]) * a4 * g2 ^ 3 * H ^ 4 +
        (2949120 : K[X]) * a4 * a6 * g2 * H ^ 4 -
        (1802240 : K[X]) * a5 ^ 2 * g2 * H ^ 4 +
        (1712128 : K[X]) * b6 * g2 ^ 3 * H ^ 3 -
        (4325376 : K[X]) * b6 * a6 * g2 * H ^ 3 -
        (1140480 : K[X]) * a5 * g2 ^ 4 * H ^ 2 +
        (3942400 : K[X]) * a5 * a6 * g2 ^ 2 * H ^ 2 -
        (1802240 : K[X]) * a5 * a6 ^ 2 * H ^ 2 +
        (1351680 : K[X]) * a6 ^ 3 * g2 -
        (1774080 : K[X]) * a6 ^ 2 * g2 ^ 3 +
        (668800 : K[X]) * a6 * g2 ^ 5 - (75240 : K[X]) * g2 ^ 7 +
        Polynomial.C κ *
          ((131072 : K[X]) * a3 * H ^ 9 -
            (65536 : K[X]) * a4 * g2 * H ^ 7 +
            (56320 : K[X]) * a5 * g2 ^ 2 * H ^ 5 -
            (180224 : K[X]) * a5 * a6 * H ^ 5 -
            (53504 : K[X]) * a6 * g2 ^ 3 * H ^ 3 +
            (135168 : K[X]) * a6 ^ 2 * g2 * H ^ 3) = 0 ∧
      (440 : K[X]) * g2 *
          ((171 : K[X]) * g2 ^ 6 - (1520 : K[X]) * a6 * g2 ^ 4 +
            (4032 : K[X]) * a6 ^ 2 * g2 ^ 2 - (3072 : K[X]) * a6 ^ 3) =
        H ^ 2 *
          ((5242880 : K[X]) * a1 * H ^ 8 - (4194304 : K[X]) * b3 * H ^ 7 -
            (1310720 : K[X]) * a2 * g2 * H ^ 6 +
            (2097152 : K[X]) * b4 * g2 * H ^ 5 +
            (1105920 : K[X]) * a3 * g2 ^ 2 * H ^ 4 -
            (1966080 : K[X]) * a3 * a6 * H ^ 4 -
            (2621440 : K[X]) * a4 * a5 * H ^ 4 -
            (1802240 : K[X]) * b5 * g2 ^ 2 * H ^ 3 +
            (2621440 : K[X]) * b5 * a6 * H ^ 3 +
            (3145728 : K[X]) * a5 * b6 * H ^ 3 -
            (1044480 : K[X]) * a4 * g2 ^ 3 * H ^ 2 +
            (2949120 : K[X]) * a4 * a6 * g2 * H ^ 2 -
            (1802240 : K[X]) * a5 ^ 2 * g2 * H ^ 2 +
            (1712128 : K[X]) * b6 * g2 ^ 3 * H -
            (4325376 : K[X]) * b6 * a6 * g2 * H -
            (1140480 : K[X]) * a5 * g2 ^ 4 +
            (3942400 : K[X]) * a5 * a6 * g2 ^ 2 -
            (1802240 : K[X]) * a5 * a6 ^ 2 +
            Polynomial.C κ *
              ((131072 : K[X]) * a3 * H ^ 7 -
                (65536 : K[X]) * a4 * g2 * H ^ 5 +
                (56320 : K[X]) * a5 * g2 ^ 2 * H ^ 3 -
                (180224 : K[X]) * a5 * a6 * H ^ 3 -
                (53504 : K[X]) * a6 * g2 ^ 3 * H +
                (135168 : K[X]) * a6 ^ 2 * g2 * H)) := by
  have hI' := hI0
  simp only [alignedSeventhDefect810, hg2] at hI'
  have hclear :
      (5242880 : K[X]) * a1 * H ^ 10 - (4194304 : K[X]) * b3 * H ^ 9 -
          (1310720 : K[X]) * a2 * g2 * H ^ 8 +
          (2097152 : K[X]) * b4 * g2 * H ^ 7 +
          (1105920 : K[X]) * a3 * g2 ^ 2 * H ^ 6 -
          (1966080 : K[X]) * a3 * a6 * H ^ 6 -
          (2621440 : K[X]) * a4 * a5 * H ^ 6 -
          (1802240 : K[X]) * b5 * g2 ^ 2 * H ^ 5 +
          (2621440 : K[X]) * b5 * a6 * H ^ 5 +
          (3145728 : K[X]) * a5 * b6 * H ^ 5 -
          (1044480 : K[X]) * a4 * g2 ^ 3 * H ^ 4 +
          (2949120 : K[X]) * a4 * a6 * g2 * H ^ 4 -
          (1802240 : K[X]) * a5 ^ 2 * g2 * H ^ 4 +
          (1712128 : K[X]) * b6 * g2 ^ 3 * H ^ 3 -
          (4325376 : K[X]) * b6 * a6 * g2 * H ^ 3 -
          (1140480 : K[X]) * a5 * g2 ^ 4 * H ^ 2 +
          (3942400 : K[X]) * a5 * a6 * g2 ^ 2 * H ^ 2 -
          (1802240 : K[X]) * a5 * a6 ^ 2 * H ^ 2 +
          (1351680 : K[X]) * a6 ^ 3 * g2 -
          (1774080 : K[X]) * a6 ^ 2 * g2 ^ 3 +
          (668800 : K[X]) * a6 * g2 ^ 5 - (75240 : K[X]) * g2 ^ 7 +
          Polynomial.C κ *
            ((131072 : K[X]) * a3 * H ^ 9 -
              (65536 : K[X]) * a4 * g2 * H ^ 7 +
              (56320 : K[X]) * a5 * g2 ^ 2 * H ^ 5 -
              (180224 : K[X]) * a5 * a6 * H ^ 5 -
              (53504 : K[X]) * a6 * g2 ^ 3 * H ^ 3 +
              (135168 : K[X]) * a6 ^ 2 * g2 * H ^ 3) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hH)
    rw [mul_zero]
    linear_combination hI' -
      H ^ 14 *
        ((28672 : K[X]) * a4 * H ^ 4 - (39424 : K[X]) * a5 * g2 * H ^ 2 -
          (19712 : K[X]) * a6 ^ 2 + (46816 : K[X]) * a6 * g2 ^ 2 -
          (13167 : K[X]) * g2 ^ 4) * hfac
  exact ⟨hclear, by linear_combination -hclear⟩

/-! ## Source-facing seventh-row packets -/

/-- Source-facing squared weight-forty-nine integral of a normalized
aligned scale-two `(8,10)` source: the degree-`10` row is consumed into
`I² = κ₆ H⁴⁹` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedSeventhFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ : K),
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
          Polynomial.C κ₅ * H ^ 21 ∧
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₆ * H ^ 49 := by
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
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, aligned_q9_solved_810 haligned, hM, hE4,
    hF2, hG, hI2⟩

/-- Exact square-chamber seventh packet of a normalized aligned
scale-two `(8,10)` source: on top of `p₇ = h₀⁴ g₁`,
`q₉ = (5/4) g₁ h₀⁶`, and the previous packet, the consumed degree-`10`
row gives the polynomial square root `I = ν₂ h₀⁴⁹` with `ν₂² = κ₆` and
the cleared seventh row (with `p₁` at `h₀²⁰` and `q₃` at `h₀¹⁸`), the
carried root collapse `g₁ = p₆ = 0`, and the carried descents
`h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedSeventhFace_squareChamber_packet
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
    ∃ (κ μ κ₆ ν₂ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ν₂ ^ 2 = κ₆ ∧
        (5242880 : K[X]) * p.coeff 1 * h0 ^ 20 -
            (4194304 : K[X]) * q.coeff 3 * h0 ^ 18 -
            (1310720 : K[X]) * p.coeff 2 * g1 * h0 ^ 16 +
            (2097152 : K[X]) * q.coeff 4 * g1 * h0 ^ 14 +
            (1105920 : K[X]) * p.coeff 3 * g1 ^ 2 * h0 ^ 12 -
            (1966080 : K[X]) * p.coeff 3 * p.coeff 6 * h0 ^ 12 -
            (2621440 : K[X]) * p.coeff 4 * p.coeff 5 * h0 ^ 12 -
            (1802240 : K[X]) * q.coeff 5 * g1 ^ 2 * h0 ^ 10 +
            (2621440 : K[X]) * q.coeff 5 * p.coeff 6 * h0 ^ 10 +
            (3145728 : K[X]) * p.coeff 5 * q.coeff 6 * h0 ^ 10 -
            (1044480 : K[X]) * p.coeff 4 * g1 ^ 3 * h0 ^ 8 +
            (2949120 : K[X]) * p.coeff 4 * p.coeff 6 * g1 * h0 ^ 8 -
            (1802240 : K[X]) * p.coeff 5 ^ 2 * g1 * h0 ^ 8 +
            (1712128 : K[X]) * q.coeff 6 * g1 ^ 3 * h0 ^ 6 -
            (4325376 : K[X]) * q.coeff 6 * p.coeff 6 * g1 * h0 ^ 6 -
            (1140480 : K[X]) * p.coeff 5 * g1 ^ 4 * h0 ^ 4 +
            (3942400 : K[X]) * p.coeff 5 * p.coeff 6 * g1 ^ 2 * h0 ^ 4 -
            (1802240 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * h0 ^ 4 +
            (1351680 : K[X]) * p.coeff 6 ^ 3 * g1 -
            (1774080 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 3 +
            (668800 : K[X]) * p.coeff 6 * g1 ^ 5 -
            (75240 : K[X]) * g1 ^ 7 +
            Polynomial.C κ *
              ((131072 : K[X]) * p.coeff 3 * h0 ^ 18 -
                (65536 : K[X]) * p.coeff 4 * g1 * h0 ^ 14 +
                (56320 : K[X]) * p.coeff 5 * g1 ^ 2 * h0 ^ 10 -
                (180224 : K[X]) * p.coeff 5 * p.coeff 6 * h0 ^ 10 -
                (53504 : K[X]) * p.coeff 6 * g1 ^ 3 * h0 ^ 6 +
                (135168 : K[X]) * p.coeff 6 ^ 2 * g1 * h0 ^ 6) -
            Polynomial.C μ *
              ((28672 : K[X]) * p.coeff 4 * h0 ^ 17 -
                (39424 : K[X]) * p.coeff 5 * g1 * h0 ^ 13 -
                (19712 : K[X]) * p.coeff 6 ^ 2 * h0 ^ 9 +
                (46816 : K[X]) * p.coeff 6 * g1 ^ 2 * h0 ^ 9 -
                (13167 : K[X]) * g1 ^ 4 * h0 ^ 9) =
          Polynomial.C ν₂ * h0 ^ 21 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C ν₂ * h0 ^ 49 := by
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
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨ν₂, hν2, hI⟩ := alignedSquareSeventh_sqrt_810 hh0 hHsq hI2
  obtain ⟨hsolved7, _hfact7⟩ :=
    alignedSquareSeventh_solved_810 hh0 hHsq hp7 hI hcore
  exact ⟨κ, μ, κ₆, ν₂, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hν2,
    hsolved7, hcollapse, hdvdg1, hdvdp6, hI⟩

/-- Exact nonsquare-chamber seventh packet of a normalized aligned
scale-two `(8,10)` source: the squared weight-forty-nine constant
vanishes, the seventh defect is identically zero, and on top of
`p₇ = H² g₂` and the previous packet the consumed degree-`10` row gives
the cleared seventh row (with `p₁` at `H¹⁰` and `q₃` at `H⁹`), the
carried root collapse `g₂ = p₆ = 0` at every (simple) root of the
core, and the carried descents `H ∣ g₂`, `H ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
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
        (5242880 : K[X]) * p.coeff 1 * H ^ 10 -
            (4194304 : K[X]) * q.coeff 3 * H ^ 9 -
            (1310720 : K[X]) * p.coeff 2 * g2 * H ^ 8 +
            (2097152 : K[X]) * q.coeff 4 * g2 * H ^ 7 +
            (1105920 : K[X]) * p.coeff 3 * g2 ^ 2 * H ^ 6 -
            (1966080 : K[X]) * p.coeff 3 * p.coeff 6 * H ^ 6 -
            (2621440 : K[X]) * p.coeff 4 * p.coeff 5 * H ^ 6 -
            (1802240 : K[X]) * q.coeff 5 * g2 ^ 2 * H ^ 5 +
            (2621440 : K[X]) * q.coeff 5 * p.coeff 6 * H ^ 5 +
            (3145728 : K[X]) * p.coeff 5 * q.coeff 6 * H ^ 5 -
            (1044480 : K[X]) * p.coeff 4 * g2 ^ 3 * H ^ 4 +
            (2949120 : K[X]) * p.coeff 4 * p.coeff 6 * g2 * H ^ 4 -
            (1802240 : K[X]) * p.coeff 5 ^ 2 * g2 * H ^ 4 +
            (1712128 : K[X]) * q.coeff 6 * g2 ^ 3 * H ^ 3 -
            (4325376 : K[X]) * q.coeff 6 * p.coeff 6 * g2 * H ^ 3 -
            (1140480 : K[X]) * p.coeff 5 * g2 ^ 4 * H ^ 2 +
            (3942400 : K[X]) * p.coeff 5 * p.coeff 6 * g2 ^ 2 * H ^ 2 -
            (1802240 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 * H ^ 2 +
            (1351680 : K[X]) * p.coeff 6 ^ 3 * g2 -
            (1774080 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 3 +
            (668800 : K[X]) * p.coeff 6 * g2 ^ 5 -
            (75240 : K[X]) * g2 ^ 7 +
            Polynomial.C κ *
              ((131072 : K[X]) * p.coeff 3 * H ^ 9 -
                (65536 : K[X]) * p.coeff 4 * g2 * H ^ 7 +
                (56320 : K[X]) * p.coeff 5 * g2 ^ 2 * H ^ 5 -
                (180224 : K[X]) * p.coeff 5 * p.coeff 6 * H ^ 5 -
                (53504 : K[X]) * p.coeff 6 * g2 ^ 3 * H ^ 3 +
                (135168 : K[X]) * p.coeff 6 ^ 2 * g2 * H ^ 3) = 0 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 := by
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
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk6, hI0⟩ :=
    alignedNonsquareSeventh_defect_eq_zero_810 hH hHdegree hnsq hI2
  obtain ⟨hclear7, _hfact7⟩ :=
    alignedNonsquareSeventh_solved_810 hH hg2 hI0 hfac
  exact ⟨κ, g2, hg2, by rw [hq9, hg2]; ring, hclear7,
    hcollapse, hdvdg2, hdvdp6, hI0⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`10`
aligned row, carrying the factored transport of the septic block.
Neither chamber is excluded, the constants `κ`, `μ`, `ν₂` are preserved
where not forced, and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedSeventhFace_chamberDichotomy
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
      ∃ (κ μ ν₂ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (440 : K[X]) * g1 *
              ((171 : K[X]) * g1 ^ 6 -
                (1520 : K[X]) * p.coeff 6 * g1 ^ 4 +
                (4032 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 2 -
                (3072 : K[X]) * p.coeff 6 ^ 3) =
            h0 ^ 4 *
              ((5242880 : K[X]) * p.coeff 1 * h0 ^ 16 -
                (4194304 : K[X]) * q.coeff 3 * h0 ^ 14 -
                (1310720 : K[X]) * p.coeff 2 * g1 * h0 ^ 12 +
                (2097152 : K[X]) * q.coeff 4 * g1 * h0 ^ 10 +
                (1105920 : K[X]) * p.coeff 3 * g1 ^ 2 * h0 ^ 8 -
                (1966080 : K[X]) * p.coeff 3 * p.coeff 6 * h0 ^ 8 -
                (2621440 : K[X]) * p.coeff 4 * p.coeff 5 * h0 ^ 8 -
                (1802240 : K[X]) * q.coeff 5 * g1 ^ 2 * h0 ^ 6 +
                (2621440 : K[X]) * q.coeff 5 * p.coeff 6 * h0 ^ 6 +
                (3145728 : K[X]) * p.coeff 5 * q.coeff 6 * h0 ^ 6 -
                (1044480 : K[X]) * p.coeff 4 * g1 ^ 3 * h0 ^ 4 +
                (2949120 : K[X]) * p.coeff 4 * p.coeff 6 * g1 * h0 ^ 4 -
                (1802240 : K[X]) * p.coeff 5 ^ 2 * g1 * h0 ^ 4 +
                (1712128 : K[X]) * q.coeff 6 * g1 ^ 3 * h0 ^ 2 -
                (4325376 : K[X]) * q.coeff 6 * p.coeff 6 * g1 * h0 ^ 2 -
                (1140480 : K[X]) * p.coeff 5 * g1 ^ 4 +
                (3942400 : K[X]) * p.coeff 5 * p.coeff 6 * g1 ^ 2 -
                (1802240 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 +
                Polynomial.C κ *
                  ((131072 : K[X]) * p.coeff 3 * h0 ^ 14 -
                    (65536 : K[X]) * p.coeff 4 * g1 * h0 ^ 10 +
                    (56320 : K[X]) * p.coeff 5 * g1 ^ 2 * h0 ^ 6 -
                    (180224 : K[X]) * p.coeff 5 * p.coeff 6 * h0 ^ 6 -
                    (53504 : K[X]) * p.coeff 6 * g1 ^ 3 * h0 ^ 2 +
                    (135168 : K[X]) * p.coeff 6 ^ 2 * g1 * h0 ^ 2) -
                Polynomial.C μ *
                  ((28672 : K[X]) * p.coeff 4 * h0 ^ 13 -
                    (39424 : K[X]) * p.coeff 5 * g1 * h0 ^ 9 -
                    (19712 : K[X]) * p.coeff 6 ^ 2 * h0 ^ 5 +
                    (46816 : K[X]) * p.coeff 6 * g1 ^ 2 * h0 ^ 5 -
                    (13167 : K[X]) * g1 ^ 4 * h0 ^ 5) -
                Polynomial.C ν₂ * h0 ^ 17) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (440 : K[X]) * g2 *
              ((171 : K[X]) * g2 ^ 6 -
                (1520 : K[X]) * p.coeff 6 * g2 ^ 4 +
                (4032 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 2 -
                (3072 : K[X]) * p.coeff 6 ^ 3) =
            H ^ 2 *
              ((5242880 : K[X]) * p.coeff 1 * H ^ 8 -
                (4194304 : K[X]) * q.coeff 3 * H ^ 7 -
                (1310720 : K[X]) * p.coeff 2 * g2 * H ^ 6 +
                (2097152 : K[X]) * q.coeff 4 * g2 * H ^ 5 +
                (1105920 : K[X]) * p.coeff 3 * g2 ^ 2 * H ^ 4 -
                (1966080 : K[X]) * p.coeff 3 * p.coeff 6 * H ^ 4 -
                (2621440 : K[X]) * p.coeff 4 * p.coeff 5 * H ^ 4 -
                (1802240 : K[X]) * q.coeff 5 * g2 ^ 2 * H ^ 3 +
                (2621440 : K[X]) * q.coeff 5 * p.coeff 6 * H ^ 3 +
                (3145728 : K[X]) * p.coeff 5 * q.coeff 6 * H ^ 3 -
                (1044480 : K[X]) * p.coeff 4 * g2 ^ 3 * H ^ 2 +
                (2949120 : K[X]) * p.coeff 4 * p.coeff 6 * g2 * H ^ 2 -
                (1802240 : K[X]) * p.coeff 5 ^ 2 * g2 * H ^ 2 +
                (1712128 : K[X]) * q.coeff 6 * g2 ^ 3 * H -
                (4325376 : K[X]) * q.coeff 6 * p.coeff 6 * g2 * H -
                (1140480 : K[X]) * p.coeff 5 * g2 ^ 4 +
                (3942400 : K[X]) * p.coeff 5 * p.coeff 6 * g2 ^ 2 -
                (1802240 : K[X]) * p.coeff 5 * p.coeff 6 ^ 2 +
                Polynomial.C κ *
                  ((131072 : K[X]) * p.coeff 3 * H ^ 7 -
                    (65536 : K[X]) * p.coeff 4 * g2 * H ^ 5 +
                    (56320 : K[X]) * p.coeff 5 * g2 ^ 2 * H ^ 3 -
                    (180224 : K[X]) * p.coeff 5 * p.coeff 6 * H ^ 3 -
                    (53504 : K[X]) * p.coeff 6 * g2 ^ 3 * H +
                    (135168 : K[X]) * p.coeff 6 ^ 2 * g2 * H)) ∧
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
      normalized810ScaleTwo_alignedSeventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, _κ₆, ν₂, g1, hp7, hq9, _hν2, hsolved7,
      hcollapse, hdvdg1, hdvdp6, _hI⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, κ, μ, ν₂, g1, hp7, hq9,
      by linear_combination -hsolved7, hcollapse, hdvdg1, hdvdp6⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, hclear7, hcollapse,
      hdvdg2, hdvdp6, _hI0⟩ := hpacket
    exact Or.inr ⟨hnsq, κ, g2, hp7, hq9,
      by linear_combination -hclear7, hcollapse, hdvdg2, hdvdp6⟩

/-- Chamber-independent root jet after the consumed degree-`10` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its septic content is absorbed by the
degree-`13` collapse (`alignedSeventh_rootSeptic_absorbed_810`) — and
the new coefficients `p₁, q₃` are tied into the cleared seventh row
instead of being killed. -/
theorem normalized810ScaleTwo_alignedSeventhFace_rootJet
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
  normalized810ScaleTwo_alignedSixthFace_rootJet hsource haligned

#print axioms alignedSeventhCoefficientJacobianRow_810
#print axioms alignedSeventhDefect_weightedDerivative_identity_810
#print axioms alignedSeventhDefectRow_eq_zero_810
#print axioms alignedSeventhDefectPowerRelation_810
#print axioms alignedSeventh_factored_rootBranch_810
#print axioms alignedSeventh_rootSeptic_absorbed_810
#print axioms alignedSquareSeventh_sqrt_810
#print axioms alignedSquareSeventh_solved_810
#print axioms alignedNonsquareSeventh_defect_eq_zero_810
#print axioms alignedNonsquareSeventh_solved_810
#print axioms normalized810ScaleTwo_alignedSeventhFace_packet
#print axioms normalized810ScaleTwo_alignedSeventhFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedSeventhFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedSeventhFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedSeventhFace_rootJet

end Max11DegreeRoutes
