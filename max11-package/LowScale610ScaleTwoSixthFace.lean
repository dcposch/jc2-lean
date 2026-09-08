import LowScale610ScaleTwoFifthFace

/-! # Scale-two sixth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the fifth face supplies the degree-`10` integral
and the jet `h⁴ ∣ p₅`, `h ∣ p₄`, `h⁵ ∣ q₈`, `h² ∣ q₇`, `h⁸ ∣ q₉`.
The next Keller coefficient is the degree-`9` Jacobian row.  After the
same sextic depression that kills `z⁵`, that row is
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 2 C P' - 3 B Q' - 4 A R'
- 6 T' = 0`.  The resulting first integral clears to a polynomial
defect `W` of weight thirty.

Evaluating the second, third, fourth, and sixth defects together at
the root of `h` forces the finite initial jet `h⁴ ∣ p₅`, `h² ∣ p₄`,
`h⁶ ∣ q₈`, `h³ ∣ q₇`, `h ∣ q₆`, and `h⁸ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z⁰`/`z⁴` defect after the degree-`10` integral. -/
theorem sixthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 8).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 9).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 9) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (9 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 9 :
      Finset (ℕ × ℕ)) =
      ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3),
        (7, 2), (8, 1),
        (9, 0)} : Finset (ℕ × ℕ)) := by decide
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

/-! ## Sextic `z⁰` and decic `z⁴` coordinates -/

section Depression610Sixth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed sextic `z⁰` coefficient. -/
abbrev depressedE610 (h r a5 a4 a3 a2 a1 a0 : F) : F :=
  depressedE68 h r a5 a4 a3 a2 a1 a0

/-- Depressed decic `z⁴` coefficient. -/
def depressedT610 (h r b9 b8 b7 b6 b5 b4 : F) : F :=
  210 * r ^ 6 - 126 * (b9 / h ^ 9) * r ^ 5 +
    70 * (b8 / h ^ 8) * r ^ 4 - 35 * (b7 / h ^ 7) * r ^ 3 +
    15 * (b6 / h ^ 6) * r ^ 2 - 5 * (b5 / h ^ 5) * r + b4 / h ^ 4

/-- First residual of the degree-`9` row.  Equivalent to
`T - (5/3) E - (3/2) L D - (4/3) α C - (7/6) β B - γ A
- (10/9) A C - (5/9) B² - (3/4) L A B - (2/9) α A² + (5/81) A³`
on the second-, third-, and fourth-face integrals. -/
def epsilonResidual610 (L A B C0 D0 E0 P Q R T0 : F) : F :=
  T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
    (4 / 3 : F) * alphaResidual610 A P * C0 -
    (7 / 6 : F) * betaResidual610 L A B Q * B -
    gammaResidual610 L A B C0 P R * A -
    (10 / 9 : F) * A * C0 - (5 / 9 : F) * B ^ 2 -
    (3 / 4 : F) * L * A * B -
    (2 / 9 : F) * alphaResidual610 A P * A ^ 2 +
    (5 / 81 : F) * A ^ 3

/-- Polynomial numerator of `419904 h³⁰ ε` on the ninth-power face. -/
def localClearedSixthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 : F[X]) (lambda : F) : F[X] :=
  -(699840 : F[X]) * a0 * h ^ 30 +
    (116640 : F[X]) * a1 * a5 * h ^ 24 +
    (209952 : F[X]) * Polynomial.C lambda * a1 * h ^ 29 +
    (1166400 : F[X]) * a2 * a4 * h ^ 24 +
    (194400 : F[X]) * a2 * a5 ^ 2 * h ^ 18 -
    (349920 : F[X]) * Polynomial.C lambda * a2 * a5 * h ^ 23 -
    (559872 : F[X]) * a2 * b8 * h ^ 20 +
    (583200 : F[X]) * a3 ^ 2 * h ^ 24 -
    (1360800 : F[X]) * a3 * a4 * a5 * h ^ 18 -
    (349920 : F[X]) * Polynomial.C lambda * a3 * a4 * h ^ 23 -
    (432000 : F[X]) * a3 * a5 ^ 3 * h ^ 12 +
    (466560 : F[X]) * Polynomial.C lambda * a3 * a5 ^ 2 * h ^ 17 +
    (933120 : F[X]) * a3 * a5 * b8 * h ^ 14 -
    (489888 : F[X]) * a3 * b7 * h ^ 20 -
    (518400 : F[X]) * a4 ^ 3 * h ^ 18 +
    (518400 : F[X]) * a4 ^ 2 * a5 ^ 2 * h ^ 12 +
    (466560 : F[X]) * Polynomial.C lambda * a4 ^ 2 * a5 * h ^ 17 +
    (466560 : F[X]) * a4 ^ 2 * b8 * h ^ 14 +
    (633600 : F[X]) * a4 * a5 ^ 4 * h ^ 6 -
    (570240 : F[X]) * Polynomial.C lambda * a4 * a5 ^ 3 * h ^ 11 -
    (1244160 : F[X]) * a4 * a5 ^ 2 * b8 * h ^ 8 +
    (816480 : F[X]) * a4 * a5 * b7 * h ^ 14 -
    (419904 : F[X]) * a4 * b6 * h ^ 20 -
    (246400 : F[X]) * a5 ^ 6 +
    (133056 : F[X]) * Polynomial.C lambda * a5 ^ 5 * h ^ 5 +
    (380160 : F[X]) * a5 ^ 4 * b8 * h ^ 2 -
    (362880 : F[X]) * a5 ^ 3 * b7 * h ^ 8 +
    (349920 : F[X]) * a5 ^ 2 * b6 * h ^ 14 -
    (349920 : F[X]) * a5 * b5 * h ^ 20 +
    (419904 : F[X]) * b4 * h ^ 26

theorem coeff_depressedSextic68_zero
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 0 = E := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the sextic `z⁰` coordinate. -/
theorem depressedE610_eq_cleared
    (h a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
      (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
          1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
          36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
        (46656 * h ^ 30) := by
  simp only [depressedE610, depressedE68, sexticDepressionR610,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁴` coordinate on the
ninth-power face. -/
theorem depressedT610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
      (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
          420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
          3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
          7776 * b4 * h ^ 26) /
        (7776 * h ^ 30) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedT610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      210 * (a5 / (6 * h ^ 5)) ^ 6 -
          126 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 5 +
        70 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 4 -
          35 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 3 +
        15 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 2 -
          5 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) + b4 / h ^ 4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) := by
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh30, h7776]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh30, h7776]
    ring
  exact hrewrite

set_option maxHeartbeats 12000000 in
/-- Clearing the first integral
`T - (5/3) E - (3/2) L D - (4/3) α C - (7/6) β B - γ A
- (10/9) A C - (5/9) B² - (3/4) L A B - (2/9) α A² + (5/81) A³`
against `h³⁰` on the ninth-power face. -/
theorem sixthDefect_eq_clearedEpsilon610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (419904 : F) * h ^ 30 *
        epsilonResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4) =
      -(699840 : F) * a0 * h ^ 30 + (116640 : F) * a1 * a5 * h ^ 24 +
        (209952 : F) * lambda * a1 * h ^ 29 +
        (1166400 : F) * a2 * a4 * h ^ 24 +
        (194400 : F) * a2 * a5 ^ 2 * h ^ 18 -
        (349920 : F) * lambda * a2 * a5 * h ^ 23 -
        (559872 : F) * a2 * b8 * h ^ 20 +
        (583200 : F) * a3 ^ 2 * h ^ 24 -
        (1360800 : F) * a3 * a4 * a5 * h ^ 18 -
        (349920 : F) * lambda * a3 * a4 * h ^ 23 -
        (432000 : F) * a3 * a5 ^ 3 * h ^ 12 +
        (466560 : F) * lambda * a3 * a5 ^ 2 * h ^ 17 +
        (933120 : F) * a3 * a5 * b8 * h ^ 14 -
        (489888 : F) * a3 * b7 * h ^ 20 -
        (518400 : F) * a4 ^ 3 * h ^ 18 +
        (518400 : F) * a4 ^ 2 * a5 ^ 2 * h ^ 12 +
        (466560 : F) * lambda * a4 ^ 2 * a5 * h ^ 17 +
        (466560 : F) * a4 ^ 2 * b8 * h ^ 14 +
        (633600 : F) * a4 * a5 ^ 4 * h ^ 6 -
        (570240 : F) * lambda * a4 * a5 ^ 3 * h ^ 11 -
        (1244160 : F) * a4 * a5 ^ 2 * b8 * h ^ 8 +
        (816480 : F) * a4 * a5 * b7 * h ^ 14 -
        (419904 : F) * a4 * b6 * h ^ 20 - (246400 : F) * a5 ^ 6 +
        (133056 : F) * lambda * a5 ^ 5 * h ^ 5 +
        (380160 : F) * a5 ^ 4 * b8 * h ^ 2 -
        (362880 : F) * a5 ^ 3 * b7 * h ^ 8 +
        (349920 : F) * a5 ^ 2 * b6 * h ^ 14 -
        (349920 : F) * a5 * b5 * h ^ 20 +
        (419904 : F) * b4 * h ^ 26 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hC :
      depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
            24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
          (144 * h ^ 20) :=
    depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD0 :
      depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
            27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
            a5 ^ 5) /
          (324 * h ^ 25) :=
    depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE0 :
      depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
        (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
            1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
            36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
          (46656 * h ^ 30) :=
    depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hT :
      depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have h12A :
      (12 : F) * h ^ 10 *
          depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2 := by
    rw [hA]
    field_simp [hh, h12, hh10]
    try ring
  have h54B :
      (54 : F) * h ^ 15 *
          depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
          (10 : F) * a5 ^ 3 := by
    rw [hB]
    field_simp [hh, h54, hh15]
    try ring
  have h144C :
      (144 : F) * h ^ 20 *
          depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 : F) * a2 * h ^ 18 - (72 : F) * a3 * a5 * h ^ 12 +
          (24 : F) * a4 * a5 ^ 2 * h ^ 6 - (5 : F) * a5 ^ 4 := by
    rw [hC]
    field_simp [hh, h144, hh20]
    try ring
  have h324D :
      (324 : F) * h ^ 25 *
          depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 : F) * a1 * h ^ 24 - (108 : F) * a2 * a5 * h ^ 18 +
          (27 : F) * a3 * a5 ^ 2 * h ^ 12 -
          (6 : F) * a4 * a5 ^ 3 * h ^ 6 + a5 ^ 5 := by
    rw [hD0]
    field_simp [hh, h324, hh25]
    try ring
  have h46656E :
      (46656 : F) * h ^ 30 *
          depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0 =
        (46656 : F) * a0 * h ^ 30 - (7776 : F) * a1 * a5 * h ^ 24 +
          (1296 : F) * a2 * a5 ^ 2 * h ^ 18 -
          (216 : F) * a3 * a5 ^ 3 * h ^ 12 +
          (36 : F) * a4 * a5 ^ 4 * h ^ 6 - (5 : F) * a5 ^ 6 := by
    rw [hE0]
    field_simp [hh, h46656, hh30]
    try ring
  have h7776T :
      (7776 : F) * h ^ 30 *
          depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 =
        -(175 : F) * a5 ^ 6 + (42 : F) * lambda * a5 ^ 5 * h ^ 5 +
          (420 : F) * a5 ^ 4 * b8 * h ^ 2 -
          (1260 : F) * a5 ^ 3 * b7 * h ^ 8 +
          (3240 : F) * a5 ^ 2 * b6 * h ^ 14 -
          (6480 : F) * a5 * b5 * h ^ 20 +
          (7776 : F) * b4 * h ^ 26 := by
    rw [hT]
    field_simp [hh, h7776, hh30]
    try ring
  have h18alpha :
      (18 : F) * h ^ 10 *
          alphaResidual610
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedP610 h (sexticDepressionR610 h a5) b9 b8) =
        (18 : F) * b8 * h ^ 2 - (30 : F) * a4 * h ^ 6 +
          (9 : F) * lambda * a5 * h ^ 5 - (10 : F) * a5 ^ 2 :=
    secondDefect_eq_clearedAlpha610 h a5 a4 b9 b8 lambda hh hN
  have h648beta :
      (648 : F) * h ^ 15 *
          betaResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7) =
        (520 : F) * a5 ^ 3 - (864 : F) * a5 * b8 * h ^ 2 -
          (351 : F) * lambda * a5 ^ 2 * h ^ 5 +
          (720 : F) * a4 * a5 * h ^ 6 + (648 : F) * b7 * h ^ 8 +
          (324 : F) * lambda * a4 * h ^ 11 -
          (1080 : F) * a3 * h ^ 12 :=
    thirdDefect_eq_clearedBeta610 h a5 a4 a3 b9 b8 b7 lambda hh hN
  have h432gamma :
      (432 : F) * h ^ 20 *
          gammaResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
            (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
            (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7
              b6) =
        -(360 : F) * a5 ^ 4 + (576 : F) * a5 ^ 2 * b8 * h ^ 2 +
          (216 : F) * lambda * a5 ^ 3 * h ^ 5 -
          (576 : F) * a4 * b8 * h ^ 8 - (504 : F) * a5 * b7 * h ^ 8 -
          (432 : F) * lambda * a5 * a4 * h ^ 11 +
          (720 : F) * a4 ^ 2 * h ^ 12 +
          (360 : F) * a5 * a3 * h ^ 12 + (432 : F) * b6 * h ^ 14 +
          (216 : F) * lambda * a3 * h ^ 17 -
          (720 : F) * a2 * h ^ 18 :=
    fourthDefect_eq_clearedGamma610 h a5 a4 a3 a2 b9 b8 b7 b6 lambda
      hh hN
  have h419904T :
      (419904 : F) * h ^ 30 *
          depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 =
        -(9450 : F) * a5 ^ 6 + (2268 : F) * lambda * a5 ^ 5 * h ^ 5 +
          (22680 : F) * a5 ^ 4 * b8 * h ^ 2 -
          (68040 : F) * a5 ^ 3 * b7 * h ^ 8 +
          (174960 : F) * a5 ^ 2 * b6 * h ^ 14 -
          (349920 : F) * a5 * b5 * h ^ 20 +
          (419904 : F) * b4 * h ^ 26 := by
    have hscale :
        (419904 : F) * h ^ 30 *
            depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5 b4 =
          (54 : F) *
            ((7776 : F) * h ^ 30 *
              depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
                b5 b4) := by
      ring
    rw [hscale, h7776T]
    ring
  have h699840E :
      (699840 : F) * h ^ 30 *
          depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0 =
        (699840 : F) * a0 * h ^ 30 - (116640 : F) * a1 * a5 * h ^ 24 +
          (19440 : F) * a2 * a5 ^ 2 * h ^ 18 -
          (3240 : F) * a3 * a5 ^ 3 * h ^ 12 +
          (540 : F) * a4 * a5 ^ 4 * h ^ 6 - (75 : F) * a5 ^ 6 := by
    have hscale :
        (699840 : F) * h ^ 30 *
            depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 a0 =
          (15 : F) *
            ((46656 : F) * h ^ 30 *
              depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
                a1 a0) := by
      ring
    rw [hscale, h46656E]
    ring
  have h209952D :
      (209952 : F) * lambda * h ^ 30 *
          depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
            a1 =
        (209952 : F) * lambda * a1 * h ^ 29 -
          (69984 : F) * lambda * a2 * a5 * h ^ 23 +
          (17496 : F) * lambda * a3 * a5 ^ 2 * h ^ 17 -
          (3888 : F) * lambda * a4 * a5 ^ 3 * h ^ 11 +
          (648 : F) * lambda * a5 ^ 5 * h ^ 5 := by
    have hscale :
        (209952 : F) * lambda * h ^ 30 *
            depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 =
          (648 : F) * lambda * h ^ 5 *
            ((324 : F) * h ^ 25 *
              depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
                a1) := by
      ring
    rw [hscale, h324D]
    ring
  have h559872alphaC :
      (559872 : F) * h ^ 30 *
          (alphaResidual610
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedP610 h (sexticDepressionR610 h a5) b9 b8) *
            depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
              a2) =
        (216 : F) *
          ((18 : F) * b8 * h ^ 2 - (30 : F) * a4 * h ^ 6 +
              (9 : F) * lambda * a5 * h ^ 5 - (10 : F) * a5 ^ 2) *
            ((144 : F) * a2 * h ^ 18 - (72 : F) * a3 * a5 * h ^ 12 +
              (24 : F) * a4 * a5 ^ 2 * h ^ 6 -
              (5 : F) * a5 ^ 4) := by
    have hscale :
        (559872 : F) * h ^ 30 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9
                  b8) *
              depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2) =
          (216 : F) *
            ((18 : F) * h ^ 10 *
                alphaResidual610
                  (depressedA610 h (sexticDepressionR610 h a5) a5
                    a4)
                  (depressedP610 h (sexticDepressionR610 h a5) b9
                    b8)) *
              ((144 : F) * h ^ 20 *
                depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                  a2) := by
      ring
    rw [hscale, h18alpha, h144C]
  have h489888betaB :
      (489888 : F) * h ^ 30 *
          (betaResidual610
              (depressedL610 h (sexticDepressionR610 h a5) b9)
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
              (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                b7) *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
        (14 : F) *
          ((520 : F) * a5 ^ 3 - (864 : F) * a5 * b8 * h ^ 2 -
              (351 : F) * lambda * a5 ^ 2 * h ^ 5 +
              (720 : F) * a4 * a5 * h ^ 6 + (648 : F) * b7 * h ^ 8 +
              (324 : F) * lambda * a4 * h ^ 11 -
              (1080 : F) * a3 * h ^ 12) *
            ((54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
              (10 : F) * a5 ^ 3) := by
    have hscale :
        (489888 : F) * h ^ 30 *
            (betaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                  b7) *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
          (14 : F) *
            ((648 : F) * h ^ 15 *
                betaResidual610
                  (depressedL610 h (sexticDepressionR610 h a5) b9)
                  (depressedA610 h (sexticDepressionR610 h a5) a5
                    a4)
                  (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                    a3)
                  (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                    b7)) *
              ((54 : F) * h ^ 15 *
                depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3) := by
      ring
    rw [hscale, h648beta, h54B]
  have h419904gammaA :
      (419904 : F) * h ^ 30 *
          (gammaResidual610
              (depressedL610 h (sexticDepressionR610 h a5) b9)
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
              (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2)
              (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
              (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7
                b6) *
            depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
        (81 : F) *
          (-(360 : F) * a5 ^ 4 + (576 : F) * a5 ^ 2 * b8 * h ^ 2 +
              (216 : F) * lambda * a5 ^ 3 * h ^ 5 -
              (576 : F) * a4 * b8 * h ^ 8 -
              (504 : F) * a5 * b7 * h ^ 8 -
              (432 : F) * lambda * a5 * a4 * h ^ 11 +
              (720 : F) * a4 ^ 2 * h ^ 12 +
              (360 : F) * a5 * a3 * h ^ 12 +
              (432 : F) * b6 * h ^ 14 +
              (216 : F) * lambda * a3 * h ^ 17 -
              (720 : F) * a2 * h ^ 18) *
            ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) := by
    have hscale :
        (419904 : F) * h ^ 30 *
            (gammaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                  a2)
                (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
                (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7
                  b6) *
              depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
          (81 : F) *
            ((432 : F) * h ^ 20 *
                gammaResidual610
                  (depressedL610 h (sexticDepressionR610 h a5) b9)
                  (depressedA610 h (sexticDepressionR610 h a5) a5
                    a4)
                  (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                    a3)
                  (depressedC610 h (sexticDepressionR610 h a5) a5 a4
                    a3 a2)
                  (depressedP610 h (sexticDepressionR610 h a5) b9
                    b8)
                  (depressedR610 h (sexticDepressionR610 h a5) b9 b8
                    b7 b6)) *
              ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5
                  a4) := by
      ring
    rw [hscale, h432gamma, h12A]
  have h466560AC :
      (466560 : F) * h ^ 30 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
            depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
              a2) =
        (270 : F) *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) *
            ((144 : F) * a2 * h ^ 18 - (72 : F) * a3 * a5 * h ^ 12 +
              (24 : F) * a4 * a5 ^ 2 * h ^ 6 -
              (5 : F) * a5 ^ 4) := by
    have hscale :
        (466560 : F) * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2) =
          (270 : F) *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5 a4) *
              ((144 : F) * h ^ 20 *
                depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                  a2) := by
      ring
    rw [hscale, h12A, h144C]
  have h233280B2 :
      (233280 : F) * h ^ 30 *
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) ^ 2 =
        (80 : F) *
          ((54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
              (10 : F) * a5 ^ 3) ^ 2 := by
    have hscale :
        (233280 : F) * h ^ 30 *
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) ^
              2 =
          (80 : F) *
            ((54 : F) * h ^ 15 *
                depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3) ^ 2 := by
      field_simp [hh, h54, hh15, hh30]
      ring
    rw [hscale, h54B]
  have h104976lamAB :
      (104976 : F) * lambda * h ^ 30 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
        (162 : F) * lambda * h ^ 5 *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) *
            ((54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
              (10 : F) * a5 ^ 3) := by
    have hscale :
        (104976 : F) * lambda * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
          (162 : F) * lambda * h ^ 5 *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5 a4) *
              ((54 : F) * h ^ 15 *
                depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3) := by
      ring
    rw [hscale, h12A, h54B]
  have h93312alphaA2 :
      (93312 : F) * h ^ 30 *
          (alphaResidual610
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedP610 h (sexticDepressionR610 h a5) b9 b8) *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^
              2) =
        (36 : F) *
          ((18 : F) * b8 * h ^ 2 - (30 : F) * a4 * h ^ 6 +
              (9 : F) * lambda * a5 * h ^ 5 - (10 : F) * a5 ^ 2) *
            ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) ^ 2 := by
    have hscale :
        (93312 : F) * h ^ 30 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9
                  b8) *
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^
                2) =
          (36 : F) *
            ((18 : F) * h ^ 10 *
                alphaResidual610
                  (depressedA610 h (sexticDepressionR610 h a5) a5
                    a4)
                  (depressedP610 h (sexticDepressionR610 h a5) b9
                    b8)) *
              ((12 : F) * h ^ 10 *
                  depressedA610 h (sexticDepressionR610 h a5) a5
                    a4) ^ 2 := by
      field_simp [hh, h12, h18, hh10, hh30]
      ring
    rw [hscale, h18alpha, h12A]
  have h25920A3 :
      (25920 : F) * h ^ 30 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 3 =
        (15 : F) *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) ^ 3 := by
    have hscale :
        (25920 : F) * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 3 =
          (15 : F) *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5
                  a4) ^ 3 := by
      field_simp [hh, h12, hh10, hh30]
      ring
    rw [hscale, h12A]
  have hdiff :
      (419904 : F) * h ^ 30 *
          epsilonResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
            (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1)
            (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 a0)
            (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
            (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
            (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
            (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5 b4) =
        (419904 : F) * h ^ 30 *
            depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5 b4 -
          (699840 : F) * h ^ 30 *
            depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 a0 +
          (209952 : F) * lambda * h ^ 30 *
            depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 -
          (559872 : F) * h ^ 30 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9
                  b8) *
              depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2) -
          (489888 : F) * h ^ 30 *
            (betaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                  b7) *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) -
          (419904 : F) * h ^ 30 *
            (gammaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                  a2)
                (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
                (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7
                  b6) *
              depressedA610 h (sexticDepressionR610 h a5) a5 a4) -
          (466560 : F) * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2) -
          (233280 : F) * h ^ 30 *
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) ^
              2 +
          (104976 : F) * lambda * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) -
          (93312 : F) * h ^ 30 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9
                  b8) *
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^
                2) +
          (25920 : F) * h ^ 30 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^
              3 := by
    simp only [epsilonResidual610, hL]
    field_simp [h2, h3, h4, h6, h8, h9, h81]
    ring
  rw [hdiff, h419904T, h699840E, h209952D, h559872alphaC, h489888betaB,
    h419904gammaA, h466560AC, h233280B2, h104976lamAB, h93312alphaA2,
    h25920A3]
  ring

end Depression610Sixth

/-! ## Degree-`9` depressed Jacobian coefficient -/

section DepressedRow610Sixth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`9` Jacobian coefficient is
exactly `10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 2 C P' - 3 B Q'
- 4 A R' - 6 T'`. -/
theorem differentialJacobian_coeff_9_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 9 =
      (10 : F) * d (f.coeff 0) + (9 : F) * g.coeff 9 * d (f.coeff 1) +
        (8 : F) * g.coeff 8 * d (f.coeff 2) +
        (7 : F) * g.coeff 7 * d (f.coeff 3) +
        (6 : F) * g.coeff 6 * d (f.coeff 4) -
          (2 : F) * f.coeff 2 * d (g.coeff 8) -
          (3 : F) * f.coeff 3 * d (g.coeff 7) -
          (4 : F) * f.coeff 4 * d (g.coeff 6) -
          (6 : F) * d (g.coeff 4) := by
  have hfd_high : ∀ n, 5 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf5]
    · have : 6 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq6 | hlt6
      · subst n
        simpa [hf6, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 6 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 6 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem09 : ((0, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem18 : ((1, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem27 : ((2, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem36 : ((3, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem45 : ((4, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem54 : ((5, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 9 =
        (10 : F) * d (f.coeff 0) +
          (9 : F) * g.coeff 9 * d (f.coeff 1) +
          (8 : F) * g.coeff 8 * d (f.coeff 2) +
          (7 : F) * g.coeff 7 * d (f.coeff 3) +
          (6 : F) * g.coeff 6 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne09_18 : ((0, 9) : ℕ × ℕ) ≠ (1, 8) := by decide
    have hne09_27 : ((0, 9) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne09_36 : ((0, 9) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne09_45 : ((0, 9) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne18_27 : ((1, 8) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne18_36 : ((1, 8) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne18_45 : ((1, 8) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne27_36 : ((2, 7) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne27_45 : ((2, 7) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne36_45 : ((3, 6) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hsubset :
        ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem09
      · subst b; exact hmem18
      · subst b; exact hmem27
      · subst b; exact hmem36
      · subst b; exact hmem45
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne09 : b ≠ (0, 9) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne18 : b ≠ (1, 8) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne27 : b ≠ (2, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne36 : b ≠ (3, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne45 : b ≠ (4, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne09
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne18
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne27
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne36
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne45
          ext
          · exact h4
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 5 := by
      rw [Finset.sum_insert (by simp [hne09_18, hne09_27, hne09_36, hne09_45]),
        Finset.sum_insert (by simp [hne18_27, hne18_36, hne18_45]),
        Finset.sum_insert (by simp [hne27_36, hne27_45]),
        Finset.sum_insert (by simp [hne36_45]), Finset.sum_singleton]
      ring
    have hder9 : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    have hder8 : g.derivative.coeff 8 = (9 : F) * g.coeff 9 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : g.derivative.coeff 7 = (8 : F) * g.coeff 8 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder9, hder8, hder7, hder6, hder5]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 9 =
        (2 : F) * f.coeff 2 * d (g.coeff 8) +
          (3 : F) * f.coeff 3 * d (g.coeff 7) +
          (4 : F) * f.coeff 4 * d (g.coeff 6) +
          (6 : F) * d (g.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne18_27 : ((1, 8) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne18_36 : ((1, 8) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne18_54 : ((1, 8) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne27_36 : ((2, 7) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne27_54 : ((2, 7) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne36_54 : ((3, 6) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hsubset : ({(1, 8), (2, 7), (3, 6), (5, 4)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem18
      · subst b; exact hmem27
      · subst b; exact hmem36
      · subst b; exact hmem54
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(1, 8), (2, 7), (3, 6), (5, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne18 : b ≠ (1, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne27 : b ≠ (2, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne36 : b ≠ (3, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne54 : b ≠ (5, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne18
            ext
            · exact h1
            · omega
          have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne27
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne36
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne54
            ext
            · exact h5
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 8), (2, 7), (3, 6), (5, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 1 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 4 := by
      rw [Finset.sum_insert (by simp [hne18_27, hne18_36, hne18_54]),
        Finset.sum_insert (by simp [hne27_36, hne27_54]),
        Finset.sum_insert (by simp [hne36_54]), Finset.sum_singleton]
      ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder1, hder2,
      hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem epsilonResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R T0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hrow : (10 : F) * d E0 + (9 : F) * L * d D0 +
        (8 : F) * P * d C0 + (7 : F) * Q * d B +
        (6 : F) * R * d A - (2 : F) * C0 * d P -
        (3 : F) * B * d Q - (4 : F) * A * d R -
        (6 : F) * d T0 = 0) :
    d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h10 : d (10 : F) = 0 := d.map_natCast 10
  have h18 : d (18 : F) = 0 := d.map_natCast 18
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h100 : d (100 : F) = 0 := d.map_natCast 100
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h109 : d (10 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h10]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h581 : d (5 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h5]
  have h259 : d (25 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h25]
  have h2518 : d (25 / 18 : F) = 0 := by
    simp [Derivation.leibniz_div, h18, h25]
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h10081 : d (100 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h100]
  have hP0 : d P - (5 / 3 : F) * d A = 0 := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    exact halpha'
  have hQ0 : d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
    have hbeta' :
        d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
      simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    exact hbeta'
  have hG0 :
      d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
        (4 / 3 : F) * A * d P - (4 / 3 : F) * P * d A +
        (10 / 3 : F) * A * d A = 0 := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]
    ring
  have heps :
      epsilonResidual610 L A B C0 D0 E0 P Q R T0 =
        T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
          (4 / 3 : F) * P * C0 - (7 / 6 : F) * Q * B - R * A +
          (25 / 9 : F) * A * C0 + (25 / 18 : F) * (B * B) +
          (5 / 2 : F) * L * A * B + (10 / 9 : F) * P * (A * A) -
          (100 / 81 : F) * (A * A * A) := by
    simp only [epsilonResidual610, alphaResidual610, betaResidual610,
      gammaResidual610, pow_two, pow_three]
    ring
  rw [heps]
  simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
    h109, h34, h29, h581, h259, h2518, h52, h10081, zero_mul,
    add_zero, mul_zero, hsq, hcub]
  linear_combination (-1 / 6 : F) * hrow +
    (-(5 / 3 : F) * C0 - (10 / 9 : F) * (A * A)) * hP0 +
    (-(5 / 3 : F) * B) * hQ0 + (-(5 / 3 : F) * A) * hG0

end DepressedRow610Sixth

/-! ## Affine depression of a degree-ten source, `z⁴` coefficient -/

section AffineDecic610Sixth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁴` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff4_610
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 4 =
      210 * r ^ 6 - 126 * (p.coeff 9 / h ^ 9) * r ^ 5 +
        70 * (p.coeff 8 / h ^ 8) * r ^ 4 -
        35 * (p.coeff 7 / h ^ 7) * r ^ 3 +
        15 * (p.coeff 6 / h ^ 6) * r ^ 2 -
        5 * (p.coeff 5 / h ^ 5) * r + p.coeff 4 / h ^ 4 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6 - C (p.coeff 5) * X ^ 5 -
      C (p.coeff 4) * X ^ 4
  have hplow : ∀ n, 4 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h4 | hlt4
    · subst n
      simp
    · have : 5 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h5 | hlt5
      · subst n
        simp
      · have : 6 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h6 | hlt6
        · subst n
          simp
        · have : 7 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h7 | hlt7
          · subst n
            simp
          · have : 8 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h8 | hlt8
            · subst n
              simp
            · have : 9 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h9 | hlt9
              · subst n
                simp
              · have : 10 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                · subst n
                  simp [hp10]
                · simp [hp_high n (by omega), show n ≠ 10 by omega,
                    show n ≠ 9 by omega, show n ≠ 8 by omega,
                    show n ≠ 7 by omega, show n ≠ 6 by omega,
                    show n ≠ 5 by omega, show n ≠ 4 by omega]
  have hplowDeg : plow.natDegree ≤ 3 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + C (p.coeff 5) * X ^ 5 +
        C (p.coeff 4) * X ^ 4 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H I J s : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s +
            H.comp s + I.comp s + J.comp s := by
      have h1 : (A + B + D + E + G + H + I + J).comp s =
          (A + B + D + E + G + H + I).comp s + J.comp s := add_comp
      have h2 : (A + B + D + E + G + H + I).comp s =
          (A + B + D + E + G + H).comp s + I.comp s := add_comp
      have h3 : (A + B + D + E + G + H).comp s =
          (A + B + D + E + G).comp s + H.comp s := add_comp
      have h4 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h5 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h6 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h7 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4, h5, h6, h7]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 4 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 3 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 3 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 4 ≤ n))
  have h10_4 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 4 =
        210 * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 4 hh]
    have hle : (4 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 4 = 210 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]
    ring
  have h9_4 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 4 =
        -126 * (p.coeff 9 / h ^ 9) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 4 hh]
    have hle : (4 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 4 = 126 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h8_4 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 4 =
        70 * (p.coeff 8 / h ^ 8) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 4 hh]
    have hle : (4 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 4 = 70 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h7_4 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 4 =
        -35 * (p.coeff 7 / h ^ 7) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 4 hh]
    have hle : (4 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 4 = 35 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]
    ring
  have h6_4 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 4 =
        15 * (p.coeff 6 / h ^ 6) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 4 hh]
    have hle : (4 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 4 = 15 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h5_4 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 4 =
        -5 * (p.coeff 5 / h ^ 5) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 4 hh]
    have hle : (4 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 4 = 5 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
  have h4_4 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 4 =
        p.coeff 4 / h ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 4 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add, h10_4, h9_4, h8_4, h7_4, h6_4, h5_4, h4_4, hlow 4 (by omega)]
  ring

end AffineDecic610Sixth

/-! ## Local scalar identities at a simple root -/

section SixthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The fifth-face jet reduces `M`, `T`, `U`, and `W` to a finite scalar
system in `(w, a₄s, s, u₇, b₆)`.  That system forces `a₄s`, `s`, `u₇`,
and `b₆` to vanish. -/
theorem sixthFace_rootScalars_vanish610
    (w a4s s u7 b6 : F)
    (hM : (18 : F) * s - (30 : F) * a4s = 0)
    (hT : (648 : F) * u7 = 0)
    (hU : (720 : F) * a4s ^ 2 - (576 : F) * a4s * s + (432 : F) * b6 -
        (504 : F) * u7 * w = 0)
    (hW : -(518400 : F) * a4s ^ 3 + (466560 : F) * a4s ^ 2 * s -
        (419904 : F) * a4s * b6 + (816480 : F) * a4s * u7 * w = 0) :
    a4s = 0 ∧ s = 0 ∧ u7 = 0 ∧ b6 = 0 := by
  have hid :
      -(518400 : F) * a4s ^ 3 + (466560 : F) * a4s ^ 2 * s -
            (419904 : F) * a4s * b6 + (816480 : F) * a4s * u7 * w +
          (972 : F) * a4s *
            ((720 : F) * a4s ^ 2 - (576 : F) * a4s * s +
              (432 : F) * b6 - (504 : F) * u7 * w) +
          (5184 : F) * a4s ^ 2 * ((18 : F) * s - (30 : F) * a4s) -
          (504 : F) * a4s * w * ((648 : F) * u7) =
        (25920 : F) * a4s ^ 3 := by
    ring
  have hcub : (25920 : F) * a4s ^ 3 = 0 := by
    rw [← hid]
    linear_combination hW + (972 : F) * a4s * hU +
      (5184 : F) * a4s ^ 2 * hM - (504 : F) * a4s * w * hT
  have h25920 : (25920 : F) ≠ 0 := by norm_num
  have ha4s0 : a4s = 0 := by
    have ha3 : a4s ^ 3 = 0 :=
      (mul_eq_zero.mp hcub).resolve_left h25920
    have hsq : (a4s ^ 2) * a4s = 0 := by
      convert ha3 using 1
      ring
    rcases mul_eq_zero.mp hsq with hsq' | ha
    · exact sq_eq_zero_iff.mp hsq'
    · exact ha
  have hs0 : s = 0 := by
    have h18 : (18 : F) ≠ 0 := by norm_num
    have : (18 : F) * s = 0 := by
      simpa [ha4s0] using hM
    exact (mul_eq_zero.mp this).resolve_left h18
  have hu0 : u7 = 0 := by
    have h648 : (648 : F) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hT).resolve_left h648
  have hb0 : b6 = 0 := by
    have h432 : (432 : F) ≠ 0 := by norm_num
    have : (432 : F) * b6 = 0 := by
      simpa [ha4s0, hs0, hu0] using hU
    exact (mul_eq_zero.mp this).resolve_left h432
  exact ⟨ha4s0, hs0, hu0, hb0⟩

end SixthFaceScalars610

/-! ## Source-facing sixth-face packet -/

section NonzeroSixthFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The fifth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h³⁰`. -/
theorem nonzeroFace610_sixthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ zeta : k,
      localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 30 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg4 :
      g.coeff 4 =
        depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg8' :
      g.coeff 8 =
        depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow12)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  have heps0deriv :
      ratFuncDerivation68
        (epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow9)
  obtain ⟨eps0, heps0⟩ :
      ∃ a : k,
        epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 4) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      heps0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda) =
        (419904 : RatFunc k) * hRF ^ 30 *
          epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 4) := by
    have hF := sixthDefect_eq_clearedEpsilon610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedSixthDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, epsilonResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, hf4, hf3, hf2, hf1, hf0, hg4, hg6,
      hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (419904 * eps0) * h0 ^ 30) := by
    rw [hclear, heps0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨419904 * eps0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading sextic coefficient to order four, the next sextic coefficient
to order two, the first unused decic coefficient to order six, `q₇`
to order three, `q₆` to order one, and `q₉` to order eight. -/
theorem nonzeroFace610_linearRoot_sixthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ^ 4 ∣ p.coeff 5 ∧ h0 ^ 2 ∣ p.coeff 4 ∧
      h0 ^ 6 ∣ q.coeff 8 ∧ h0 ^ 3 ∣ q.coeff 7 ∧
      h0 ∣ q.coeff 6 ∧ h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace610_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨hp5pow, hp4div, hq8pow, hq7pow, _hq9pow⟩ :=
    nonzeroFace610_linearRoot_fifthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
  obtain ⟨w, hw⟩ := hp5pow
  obtain ⟨a4s, ha4s⟩ := hp4div
  obtain ⟨s, hs⟩ := hq8pow
  obtain ⟨u7, hu7⟩ := hq7pow
  have hM0 :
      (18 : k[X]) * s - (30 : k[X]) * a4s +
          (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 2 -
        (10 : k[X]) * w ^ 2 * h0 =
        Polynomial.C alpha * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 7 hh0)
    calc
      h0 ^ 7 *
            ((18 : k[X]) * s - (30 : k[X]) * a4s +
                (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 2 -
              (10 : k[X]) * w ^ 2 * h0) =
          localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect610, hw, ha4s, hs]
        ring
      _ = Polynomial.C alpha * h0 ^ 10 := hM
      _ = h0 ^ 7 * (Polynomial.C alpha * h0 ^ 3) := by ring
  have hT0 :
      (648 : k[X]) * u7 + (720 : k[X]) * a4s * w * h0 -
          (864 : k[X]) * s * w * h0 - (1080 : k[X]) * p.coeff 3 * h0 ^ 2 +
        (324 : k[X]) * Polynomial.C lambda * a4s * h0 ^ 2 +
          (520 : k[X]) * w ^ 3 * h0 ^ 2 -
        (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 3 =
        Polynomial.C gamma * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
    calc
      h0 ^ 10 *
            ((648 : k[X]) * u7 + (720 : k[X]) * a4s * w * h0 -
                (864 : k[X]) * s * w * h0 -
              (1080 : k[X]) * p.coeff 3 * h0 ^ 2 +
                (324 : k[X]) * Polynomial.C lambda * a4s * h0 ^ 2 +
              (520 : k[X]) * w ^ 3 * h0 ^ 2 -
                (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 3) =
          localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect610, hw, ha4s, hs, hu7]
        ring
      _ = Polynomial.C gamma * h0 ^ 15 := hT
      _ = h0 ^ 10 * (Polynomial.C gamma * h0 ^ 5) := by ring
  have hU0 :
      (720 : k[X]) * a4s ^ 2 - (576 : k[X]) * a4s * s +
          (432 : k[X]) * q.coeff 6 - (504 : k[X]) * u7 * w +
        (576 : k[X]) * s * w ^ 2 * h0 + (360 : k[X]) * p.coeff 3 * w *
            h0 ^ 2 -
          (360 : k[X]) * w ^ 4 * h0 ^ 2 -
            (432 : k[X]) * Polynomial.C lambda * a4s * w * h0 ^ 2 +
          (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 3 +
            (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 3 -
          (720 : k[X]) * p.coeff 2 * h0 ^ 4 =
        Polynomial.C delta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
    calc
      h0 ^ 14 *
            ((720 : k[X]) * a4s ^ 2 - (576 : k[X]) * a4s * s +
                (432 : k[X]) * q.coeff 6 - (504 : k[X]) * u7 * w +
              (576 : k[X]) * s * w ^ 2 * h0 +
                (360 : k[X]) * p.coeff 3 * w * h0 ^ 2 -
              (360 : k[X]) * w ^ 4 * h0 ^ 2 -
                (432 : k[X]) * Polynomial.C lambda * a4s * w * h0 ^ 2 +
              (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 3 +
                (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 3 -
              (720 : k[X]) * p.coeff 2 * h0 ^ 4) =
          localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect610, hw, ha4s, hs, hu7]
        ring
      _ = Polynomial.C delta * h0 ^ 20 := hU
      _ = h0 ^ 14 * (Polynomial.C delta * h0 ^ 6) := by ring
  have hW0 :
      -(518400 : k[X]) * a4s ^ 3 + (466560 : k[X]) * a4s ^ 2 * s -
            (419904 : k[X]) * a4s * q.coeff 6 +
          (816480 : k[X]) * a4s * u7 * w +
        (-(489888 : k[X]) * p.coeff 3 * u7 +
              (518400 : k[X]) * a4s ^ 2 * w ^ 2 -
            (1244160 : k[X]) * a4s * s * w ^ 2 +
              (349920 : k[X]) * q.coeff 6 * w ^ 2 -
            (362880 : k[X]) * u7 * w ^ 3) * h0 +
          (-(1360800 : k[X]) * p.coeff 3 * a4s * w +
                (933120 : k[X]) * p.coeff 3 * s * w +
              (466560 : k[X]) * Polynomial.C lambda * a4s ^ 2 * w +
                (633600 : k[X]) * a4s * w ^ 4 +
              (380160 : k[X]) * s * w ^ 4) * h0 ^ 2 +
            ((583200 : k[X]) * p.coeff 3 ^ 2 -
                  (349920 : k[X]) * Polynomial.C lambda * p.coeff 3 *
                      a4s -
                (432000 : k[X]) * p.coeff 3 * w ^ 3 -
                  (570240 : k[X]) * Polynomial.C lambda * a4s * w ^ 3 -
                (349920 : k[X]) * q.coeff 5 * w -
                  (246400 : k[X]) * w ^ 6) * h0 ^ 3 +
              ((1166400 : k[X]) * p.coeff 2 * a4s -
                    (559872 : k[X]) * p.coeff 2 * s +
                  (466560 : k[X]) * Polynomial.C lambda * p.coeff 3 *
                      w ^ 2 +
                    (133056 : k[X]) * Polynomial.C lambda * w ^ 5) *
                  h0 ^ 4 +
                ((194400 : k[X]) * p.coeff 2 * w ^ 2 +
                    (419904 : k[X]) * q.coeff 4) * h0 ^ 5 -
                  (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 * w *
                      h0 ^ 6 +
                    (116640 : k[X]) * p.coeff 1 * w * h0 ^ 7 +
                      (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                          h0 ^ 8 -
                        (699840 : k[X]) * p.coeff 0 * h0 ^ 9 =
        Polynomial.C zeta * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 21 hh0)
    calc
      h0 ^ 21 *
            (-(518400 : k[X]) * a4s ^ 3 +
                  (466560 : k[X]) * a4s ^ 2 * s -
                (419904 : k[X]) * a4s * q.coeff 6 +
                  (816480 : k[X]) * a4s * u7 * w +
                (-(489888 : k[X]) * p.coeff 3 * u7 +
                      (518400 : k[X]) * a4s ^ 2 * w ^ 2 -
                    (1244160 : k[X]) * a4s * s * w ^ 2 +
                      (349920 : k[X]) * q.coeff 6 * w ^ 2 -
                    (362880 : k[X]) * u7 * w ^ 3) * h0 +
                  (-(1360800 : k[X]) * p.coeff 3 * a4s * w +
                        (933120 : k[X]) * p.coeff 3 * s * w +
                      (466560 : k[X]) * Polynomial.C lambda * a4s ^ 2 *
                          w +
                        (633600 : k[X]) * a4s * w ^ 4 +
                      (380160 : k[X]) * s * w ^ 4) * h0 ^ 2 +
                    ((583200 : k[X]) * p.coeff 3 ^ 2 -
                          (349920 : k[X]) * Polynomial.C lambda *
                              p.coeff 3 * a4s -
                        (432000 : k[X]) * p.coeff 3 * w ^ 3 -
                          (570240 : k[X]) * Polynomial.C lambda * a4s *
                              w ^ 3 -
                        (349920 : k[X]) * q.coeff 5 * w -
                          (246400 : k[X]) * w ^ 6) * h0 ^ 3 +
                      ((1166400 : k[X]) * p.coeff 2 * a4s -
                            (559872 : k[X]) * p.coeff 2 * s +
                          (466560 : k[X]) * Polynomial.C lambda *
                              p.coeff 3 * w ^ 2 +
                            (133056 : k[X]) * Polynomial.C lambda *
                                w ^ 5) * h0 ^ 4 +
                        ((194400 : k[X]) * p.coeff 2 * w ^ 2 +
                            (419904 : k[X]) * q.coeff 4) * h0 ^ 5 -
                          (349920 : k[X]) * Polynomial.C lambda *
                              p.coeff 2 * w * h0 ^ 6 +
                            (116640 : k[X]) * p.coeff 1 * w * h0 ^ 7 +
                              (209952 : k[X]) * Polynomial.C lambda *
                                  p.coeff 1 * h0 ^ 8 -
                                (699840 : k[X]) * p.coeff 0 * h0 ^ 9) =
          localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda := by
        simp only [localClearedSixthDefect610, hw, ha4s, hs, hu7]
        ring
      _ = Polynomial.C zeta * h0 ^ 30 := hWrel
      _ = h0 ^ 21 * (Polynomial.C zeta * h0 ^ 9) := by ring
  have hMroot : (18 : k) * s.eval a - (30 : k) * a4s.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (648 : k) * u7.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (720 : k) * (a4s.eval a) ^ 2 -
      (576 : k) * a4s.eval a * s.eval a +
        (432 : k) * (q.coeff 6).eval a -
      (504 : k) * u7.eval a * w.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  have hWroot : -(518400 : k) * (a4s.eval a) ^ 3 +
      (466560 : k) * (a4s.eval a) ^ 2 * s.eval a -
        (419904 : k) * a4s.eval a * (q.coeff 6).eval a +
      (816480 : k) * a4s.eval a * u7.eval a * w.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hW0
    simpa [hroot] using heval
  obtain ⟨ha40, hs0, hu0, hb60⟩ :=
    sixthFace_rootScalars_vanish610 (w.eval a) (a4s.eval a) (s.eval a)
      (u7.eval a) ((q.coeff 6).eval a) hMroot hTroot hUroot hWroot
  have ha4s_div : h0 ∣ a4s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 a4s a hh0degree hroot ha40
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hs0
  have hu7_div : h0 ∣ u7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u7 a hh0degree hroot hu0
  have hb6_div : h0 ∣ q.coeff 6 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
      hroot hb60
  have hp4pow2 : h0 ^ 2 ∣ p.coeff 4 := by
    obtain ⟨a41, ha41⟩ := ha4s_div
    refine ⟨a41, ?_⟩
    rw [ha4s, ha41]
    ring
  have hq8pow6 : h0 ^ 6 ∣ q.coeff 8 := by
    obtain ⟨s1, hs1⟩ := hs_div
    refine ⟨s1, ?_⟩
    rw [hs, hs1]
    ring
  have hq7pow3 : h0 ^ 3 ∣ q.coeff 7 := by
    obtain ⟨u8, hu8⟩ := hu7_div
    refine ⟨u8, ?_⟩
    rw [hu7, hu8]
    ring
  have hq9pow8 : h0 ^ 8 ∣ q.coeff 9 := by
    have h3 : (3 : k) ≠ 0 := by norm_num
    have hp5w : p.coeff 5 = h0 ^ 4 * w := hw
    have hN' :
        (3 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 5 * h0 ^ 4 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      linear_combination -this
    have hform :
        (3 : k[X]) * q.coeff 9 =
          h0 ^ 8 * ((5 : k[X]) * w - Polynomial.C lambda * h0) := by
      rw [hN', hp5w]
      ring
    have hC3 : Polynomial.C (3 : k) = (3 : k[X]) :=
      Polynomial.C_eq_natCast 3
    have hq9eq : q.coeff 9 =
        C ((3 : k)⁻¹) * ((3 : k[X]) * q.coeff 9) := by
      have hone : (C ((3 : k)⁻¹) * C (3 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h3, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((3 : k)⁻¹) * C (3 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((3 : k)⁻¹) * (C (3 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((3 : k)⁻¹) * ((3 : k[X]) * q.coeff 9) := by rw [hC3]
    refine ⟨C ((3 : k)⁻¹) *
        ((5 : k[X]) * w - Polynomial.C lambda * h0), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨⟨w, hw⟩, hp4pow2, hq8pow6, hq7pow3, hb6_div, hq9pow8⟩

/-- Source-facing sixth integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_sixthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda zeta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSixthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda =
          Polynomial.C zeta * h0 ^ 30 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨zeta, hW⟩ :=
    nonzeroFace610_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, zeta, hh0, hlambda, hh0degree, hH, hN', hW⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the sixth-face jet `h⁴ ∣ p₅`, `h² ∣ p₄`, `h⁶ ∣ q₈`,
`h³ ∣ q₇`, `h ∣ q₆`, and `h⁸ ∣ q₉`. -/
theorem normalized610ScaleTwo_nonzeroFace_sixthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 4 ∣ p.coeff 5 ∧ h0 ^ 2 ∣ p.coeff 4 ∧
        h0 ^ 6 ∣ q.coeff 8 ∧ h0 ^ 3 ∣ q.coeff 7 ∧
        h0 ∣ q.coeff 6 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized610ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp5, hp4, hq8, hq7, hq6, hq9⟩ :=
    nonzeroFace610_linearRoot_sixthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hp4, hq8,
    hq7, hq6, hq9, hN'⟩

end NonzeroSixthFace610

#print axioms sixthCoefficientJacobianRow_610
#print axioms differentialJacobian_coeff_9_monicSexticDecic
#print axioms sixthDefect_eq_clearedEpsilon610
#print axioms nonzeroFace610_sixthDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_sixthInitialPacket
#print axioms normalized610ScaleTwo_nonzeroFace_sixthDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_sixthInitialPacket

end Max11DegreeRoutes
