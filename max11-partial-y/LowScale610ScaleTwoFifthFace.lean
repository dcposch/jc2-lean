import LowScale610ScaleTwoFourthFace

/-! # Scale-two fifth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the fourth face supplies the degree-`11` integral
and the quartic jet `h³ ∣ p₅`, `h⁴ ∣ q₈`, `h ∣ q₇`, `h⁷ ∣ q₉` together
with `h¹³ ∣ p₅⁴ - 9 p₅² p₄ h⁶ + 27 p₄² h¹²`.  The next Keller
coefficient is the degree-`10` Jacobian row.  After the same sextic
depression that kills `z⁵`, that row is
`10 D' + 9 L C' + 8 P B' + 7 Q A' - 3 B P' - 4 A Q' - 6 S' = 0`.
The resulting first integral clears to a polynomial defect `V` of
weight twenty-five.

Evaluating the second, third, fourth, and fifth defects together at
the root of `h` forces the finite initial jet `h⁴ ∣ p₅`, `h ∣ p₄`,
`h⁵ ∣ q₈`, `h² ∣ q₇`, and `h⁸ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fifth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z¹`/`z⁵` defect after the degree-`11` integral. -/
theorem fifthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 9).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 10).derivative) =
      0 := by
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Sextic `z¹` and decic `z⁵` coordinates -/

section Depression610Fifth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed sextic `z¹` coefficient. -/
abbrev depressedD610 (h r a5 a4 a3 a2 a1 : F) : F :=
  depressedD68 h r a5 a4 a3 a2 a1

/-- Depressed decic `z⁵` coefficient. -/
def depressedS610 (h r b9 b8 b7 b6 b5 : F) : F :=
  -252 * r ^ 5 + 126 * (b9 / h ^ 9) * r ^ 4 -
    56 * (b8 / h ^ 8) * r ^ 3 + 21 * (b7 / h ^ 7) * r ^ 2 -
    6 * (b6 / h ^ 6) * r + b5 / h ^ 5

/-- First residual of the degree-`10` row.  Equivalent to
`S - (5/3) D - (3/2) L C - (4/3) α B - (7/6) β A - (10/9) A B - (3/8) L A²`
on the second- and third-face integrals. -/
def deltaResidual610 (L A B C0 D0 P Q S0 : F) : F :=
  S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
    (4 / 3 : F) * alphaResidual610 A P * B -
    (7 / 6 : F) * betaResidual610 L A B Q * A -
    (10 / 9 : F) * A * B - (3 / 8 : F) * L * A ^ 2

/-- Polynomial numerator of `93312 h²⁵ δ` on the ninth-power face. -/
def localClearedFifthDefect610
    (h a5 a4 a3 a2 a1 b8 b7 b6 b5 : F[X]) (lambda : F) : F[X] :=
  -(155520 : F[X]) * a1 * h ^ 24 +
    (51840 : F[X]) * a2 * a5 * h ^ 18 +
    (46656 : F[X]) * Polynomial.C lambda * a2 * h ^ 23 +
    (285120 : F[X]) * a3 * a4 * h ^ 18 +
    (23760 : F[X]) * a3 * a5 ^ 2 * h ^ 12 -
    (85536 : F[X]) * Polynomial.C lambda * a3 * a5 * h ^ 17 -
    (124416 : F[X]) * a3 * b8 * h ^ 14 -
    (190080 : F[X]) * a4 ^ 2 * a5 * h ^ 12 -
    (42768 : F[X]) * Polynomial.C lambda * a4 ^ 2 * h ^ 17 -
    (89760 : F[X]) * a4 * a5 ^ 3 * h ^ 6 +
    (121176 : F[X]) * Polynomial.C lambda * a4 * a5 ^ 2 * h ^ 11 +
    (228096 : F[X]) * a4 * a5 * b8 * h ^ 8 -
    (108864 : F[X]) * a4 * b7 * h ^ 14 +
    (68816 : F[X]) * a5 ^ 5 -
    (38709 : F[X]) * Polynomial.C lambda * a5 ^ 4 * h ^ 5 -
    (107712 : F[X]) * a5 ^ 3 * b8 * h ^ 2 +
    (99792 : F[X]) * a5 ^ 2 * b7 * h ^ 8 -
    (93312 : F[X]) * a5 * b6 * h ^ 14 +
    (93312 : F[X]) * b5 * h ^ 20

theorem coeff_depressedSextic68_one
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 1 = D := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the sextic `z¹` coordinate. -/
theorem depressedD610_eq_cleared
    (h a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
      (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
          27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
          a5 ^ 5) /
        (324 * h ^ 25) := by
  simp only [depressedD610, depressedD68, sexticDepressionR610,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁵` coordinate on the
ninth-power face. -/
theorem depressedS610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
      (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
          56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
          216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
        (216 * h ^ 25) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedS610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      -252 * (a5 / (6 * h ^ 5)) ^ 5 +
          126 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 4 -
        56 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 3 +
          21 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 2 -
        6 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) + b5 / h ^ 5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) := by
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh25, h216]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh25, h216]
    ring
  exact hrewrite

set_option maxHeartbeats 8000000 in
/-- Clearing the first integral
`S - (5/3) D - (3/2) L C - (4/3) α B - (7/6) β A - (10/9) A B - (3/8) L A²`
against `h²⁵` on the ninth-power face. -/
theorem fifthDefect_eq_clearedDelta610
    (h a5 a4 a3 a2 a1 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (93312 : F) * h ^ 25 *
        deltaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5) =
      -(155520 : F) * a1 * h ^ 24 + (51840 : F) * a2 * a5 * h ^ 18 +
        (46656 : F) * lambda * a2 * h ^ 23 +
        (285120 : F) * a3 * a4 * h ^ 18 +
        (23760 : F) * a3 * a5 ^ 2 * h ^ 12 -
        (85536 : F) * lambda * a3 * a5 * h ^ 17 -
        (124416 : F) * a3 * b8 * h ^ 14 -
        (190080 : F) * a4 ^ 2 * a5 * h ^ 12 -
        (42768 : F) * lambda * a4 ^ 2 * h ^ 17 -
        (89760 : F) * a4 * a5 ^ 3 * h ^ 6 +
        (121176 : F) * lambda * a4 * a5 ^ 2 * h ^ 11 +
        (228096 : F) * a4 * a5 * b8 * h ^ 8 -
        (108864 : F) * a4 * b7 * h ^ 14 + (68816 : F) * a5 ^ 5 -
        (38709 : F) * lambda * a5 ^ 4 * h ^ 5 -
        (107712 : F) * a5 ^ 3 * b8 * h ^ 2 +
        (99792 : F) * a5 ^ 2 * b7 * h ^ 8 -
        (93312 : F) * a5 * b6 * h ^ 14 +
        (93312 : F) * b5 * h ^ 20 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
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
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
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
  have h216S :
      (216 : F) * h ^ 25 *
          depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 : F) * a5 ^ 5 - (7 : F) * lambda * a5 ^ 4 * h ^ 5 -
          (56 : F) * a5 ^ 3 * b8 * h ^ 2 +
          (126 : F) * a5 ^ 2 * b7 * h ^ 8 -
          (216 : F) * a5 * b6 * h ^ 14 +
          (216 : F) * b5 * h ^ 20 := by
    rw [hS]
    field_simp [hh, h216, hh25]
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
  have h93312S :
      (93312 : F) * h ^ 25 *
          depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (12096 : F) * a5 ^ 5 - (3024 : F) * lambda * a5 ^ 4 * h ^ 5 -
          (24192 : F) * a5 ^ 3 * b8 * h ^ 2 +
          (54432 : F) * a5 ^ 2 * b7 * h ^ 8 -
          (93312 : F) * a5 * b6 * h ^ 14 +
          (93312 : F) * b5 * h ^ 20 := by
    have hscale :
        (93312 : F) * h ^ 25 *
            depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5 =
          (432 : F) *
            ((216 : F) * h ^ 25 *
              depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
                b5) := by
      ring
    rw [hscale, h216S]
    ring
  have h155520D :
      (155520 : F) * h ^ 25 *
          depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (155520 : F) * a1 * h ^ 24 - (51840 : F) * a2 * a5 * h ^ 18 +
          (12960 : F) * a3 * a5 ^ 2 * h ^ 12 -
          (2880 : F) * a4 * a5 ^ 3 * h ^ 6 + (480 : F) * a5 ^ 5 := by
    have hscale :
        (155520 : F) * h ^ 25 *
            depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 =
          (480 : F) *
            ((324 : F) * h ^ 25 *
              depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
                a1) := by
      ring
    rw [hscale, h324D]
    ring
  have h46656C :
      (46656 : F) * lambda * h ^ 25 *
          depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (46656 : F) * lambda * a2 * h ^ 23 -
          (23328 : F) * lambda * a3 * a5 * h ^ 17 +
          (7776 : F) * lambda * a4 * a5 ^ 2 * h ^ 11 -
          (1620 : F) * lambda * a5 ^ 4 * h ^ 5 := by
    have hscale :
        (46656 : F) * lambda * h ^ 25 *
            depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
          (324 : F) * lambda * h ^ 5 *
            ((144 : F) * h ^ 20 *
              depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3
                a2) := by
      ring
    rw [hscale, h144C]
    ring
  have h124416alphaB :
      (124416 : F) * h ^ 25 *
          (alphaResidual610
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedP610 h (sexticDepressionR610 h a5) b9 b8) *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
        (128 : F) *
          ((18 : F) * b8 * h ^ 2 - (30 : F) * a4 * h ^ 6 +
              (9 : F) * lambda * a5 * h ^ 5 - (10 : F) * a5 ^ 2) *
            ((54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
              (10 : F) * a5 ^ 3) := by
    have hscale :
        (124416 : F) * h ^ 25 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9 b8) *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
          (128 : F) *
            ((18 : F) * h ^ 10 *
                alphaResidual610
                  (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                  (depressedP610 h (sexticDepressionR610 h a5) b9
                    b8)) *
              ((54 : F) * h ^ 15 *
                depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3) := by
      ring
    rw [hscale, h18alpha, h54B]
  have h108864betaA :
      (108864 : F) * h ^ 25 *
          (betaResidual610
              (depressedL610 h (sexticDepressionR610 h a5) b9)
              (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
              (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
              (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7) *
            depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
        (14 : F) *
          ((520 : F) * a5 ^ 3 - (864 : F) * a5 * b8 * h ^ 2 -
              (351 : F) * lambda * a5 ^ 2 * h ^ 5 +
              (720 : F) * a4 * a5 * h ^ 6 + (648 : F) * b7 * h ^ 8 +
              (324 : F) * lambda * a4 * h ^ 11 -
              (1080 : F) * a3 * h ^ 12) *
            ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) := by
    have hscale :
        (108864 : F) * h ^ 25 *
            (betaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                  b7) *
              depressedA610 h (sexticDepressionR610 h a5) a5 a4) =
          (14 : F) *
            ((648 : F) * h ^ 15 *
                betaResidual610
                  (depressedL610 h (sexticDepressionR610 h a5) b9)
                  (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                  (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                    a3)
                  (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                    b7)) *
              ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5
                  a4) := by
      ring
    rw [hscale, h648beta, h12A]
  have h103680AB :
      (103680 : F) * h ^ 25 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
        (160 : F) *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) *
            ((54 : F) * a3 * h ^ 12 - (36 : F) * a4 * a5 * h ^ 6 +
              (10 : F) * a5 ^ 3) := by
    have hscale :
        (103680 : F) * h ^ 25 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) =
          (160 : F) *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5 a4) *
              ((54 : F) * h ^ 15 *
                depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3) := by
      ring
    rw [hscale, h12A, h54B]
  have h11664A2 :
      (11664 : F) * lambda * h ^ 25 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 =
        (81 : F) * lambda * h ^ 5 *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) ^ 2 := by
    have hscale :
        (11664 : F) * lambda * h ^ 25 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 =
          (81 : F) * lambda * h ^ 5 *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5
                  a4) ^ 2 := by
      field_simp [hh, h12, hh10, hh25]
      ring
    rw [hscale, h12A]
  have hdiff :
      (93312 : F) * h ^ 25 *
          deltaResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
            (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1)
            (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
            (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
            (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5) =
        (93312 : F) * h ^ 25 *
            depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6
              b5 -
          (155520 : F) * h ^ 25 *
            depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2
              a1 +
          (46656 : F) * lambda * h ^ 25 *
            depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 -
          (124416 : F) * h ^ 25 *
            (alphaResidual610
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedP610 h (sexticDepressionR610 h a5) b9 b8) *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) -
          (108864 : F) * h ^ 25 *
            (betaResidual610
                (depressedL610 h (sexticDepressionR610 h a5) b9)
                (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
                (depressedB610 h (sexticDepressionR610 h a5) a5 a4
                  a3)
                (depressedQ610 h (sexticDepressionR610 h a5) b9 b8
                  b7) *
              depressedA610 h (sexticDepressionR610 h a5) a5 a4) -
          (103680 : F) * h ^ 25 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3) +
          (11664 : F) * lambda * h ^ 25 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 :=
    by
    simp only [deltaResidual610, hL]
    field_simp [h2, h3, h6, h8, h9]
    ring
  rw [hdiff, h93312S, h155520D, h46656C, h124416alphaB, h108864betaA,
    h103680AB, h11664A2]
  ring

end Depression610Fifth

/-! ## Degree-`10` depressed Jacobian coefficient -/

section DepressedRow610Fifth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`10` Jacobian coefficient is
exactly `10 D' + 9 L C' + 8 P B' + 7 Q A' - 3 B P' - 4 A Q' - 6 S'`. -/
theorem differentialJacobian_coeff_10_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 10 =
      (10 : F) * d (f.coeff 1) + (9 : F) * g.coeff 9 * d (f.coeff 2) +
        (8 : F) * g.coeff 8 * d (f.coeff 3) +
        (7 : F) * g.coeff 7 * d (f.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 8) -
          (4 : F) * f.coeff 4 * d (g.coeff 7) -
          (6 : F) * d (g.coeff 5) := by
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
  have hmem19 : ((1, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem28 : ((2, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem37 : ((3, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem46 : ((4, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem55 : ((5, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 10 =
        (10 : F) * d (f.coeff 1) +
          (9 : F) * g.coeff 9 * d (f.coeff 2) +
          (8 : F) * g.coeff 8 * d (f.coeff 3) +
          (7 : F) * g.coeff 7 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne19_28 : ((1, 9) : ℕ × ℕ) ≠ (2, 8) := by decide
    have hne19_37 : ((1, 9) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne19_46 : ((1, 9) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne28_37 : ((2, 8) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne28_46 : ((2, 8) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne37_46 : ((3, 7) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hsubset : ({(1, 9), (2, 8), (3, 7), (4, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (10 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem19
      · subst b; exact hmem28
      · subst b; exact hmem37
      · subst b; exact hmem46
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(1, 9), (2, 8), (3, 7), (4, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 10 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne19 : b ≠ (1, 9) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne28 : b ≠ (2, 8) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne37 : b ≠ (3, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne46 : b ≠ (4, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne19
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne28
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne37
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne46
          ext
          · exact h4
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 9), (2, 8), (3, 7), (4, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 1 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 6 := by
      rw [Finset.sum_insert (by simp [hne19_28, hne19_37, hne19_46]),
        Finset.sum_insert (by simp [hne28_37, hne28_46]),
        Finset.sum_insert (by simp [hne37_46]), Finset.sum_singleton]
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
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder9, hder8,
      hder7, hder6]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 10 =
        (3 : F) * f.coeff 3 * d (g.coeff 8) +
          (4 : F) * f.coeff 4 * d (g.coeff 7) +
          (6 : F) * d (g.coeff 5) := by
    rw [Polynomial.coeff_mul]
    have hne28_37 : ((2, 8) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne28_55 : ((2, 8) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne37_55 : ((3, 7) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hsubset : ({(2, 8), (3, 7), (5, 5)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (10 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem28
      · subst b; exact hmem37
      · subst b; exact hmem55
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(2, 8), (3, 7), (5, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 10 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne28 : b ≠ (2, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne37 : b ≠ (3, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne55 : b ≠ (5, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne28
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne37
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne55
            ext
            · exact h5
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(2, 8), (3, 7), (5, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 2 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 5 := by
      rw [Finset.sum_insert (by simp [hne28_37, hne28_55]),
        Finset.sum_insert (by simp [hne37_55]), Finset.sum_singleton]
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
      coeff_coefficientDeriv, hder2, hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem deltaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 P Q S0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hrow : (10 : F) * d D0 + (9 : F) * L * d C0 +
        (8 : F) * P * d B + (7 : F) * Q * d A -
        (3 : F) * B * d P - (4 : F) * A * d Q -
        (6 : F) * d S0 = 0) :
    d (deltaResidual610 L A B C0 D0 P Q S0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h10 : d (10 : F) = 0 := d.map_natCast 10
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
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
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
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hdelta :
      deltaResidual610 L A B C0 D0 P Q S0 =
        S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
          (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
          (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
    simp only [deltaResidual610, alphaResidual610, betaResidual610, pow_two]
    ring
  have h18 : d (18 : F) = 0 := d.map_natCast 18
  have h11 : d (11 : F) = 0 := d.map_natCast 11
  have h55 : d (55 : F) = 0 := d.map_natCast 55
  have h5518 : d (55 / 18 : F) = 0 := by
    simp [Derivation.leibniz_div, h18, h55]
  have h118 : d (11 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h11]
  rw [hdelta]
  simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
    h5518, h118, zero_mul, add_zero, mul_zero, hsq]
  linear_combination (-1 / 6 : F) * hrow + (-11 / 6 : F) * B * hP0 +
    (-11 / 6 : F) * A * hQ0

end DepressedRow610Fifth

/-! ## Affine depression of a degree-ten source, `z⁵` coefficient -/

section AffineDecic610Fifth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁵` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff5_610
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 5 =
      -252 * r ^ 5 + 126 * (p.coeff 9 / h ^ 9) * r ^ 4 -
        56 * (p.coeff 8 / h ^ 8) * r ^ 3 +
        21 * (p.coeff 7 / h ^ 7) * r ^ 2 -
        6 * (p.coeff 6 / h ^ 6) * r + p.coeff 5 / h ^ 5 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6 - C (p.coeff 5) * X ^ 5
  have hplow : ∀ n, 5 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h5 | hlt5
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
                  show n ≠ 5 by omega]
  have hplowDeg : plow.natDegree ≤ 4 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + C (p.coeff 5) * X ^ 5 + plow := by
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
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H I s : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s +
            H.comp s + I.comp s := by
      have h1 : (A + B + D + E + G + H + I).comp s =
          (A + B + D + E + G + H).comp s + I.comp s := add_comp
      have h2 : (A + B + D + E + G + H).comp s =
          (A + B + D + E + G).comp s + H.comp s := add_comp
      have h3 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h4 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h5 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h6 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4, h5, h6]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 5 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 4 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 4 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 5 ≤ n))
  have h10_5 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 5 =
        -252 * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 5 hh]
    have hle : (5 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 5 = 252 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]
    ring
  have h9_5 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 5 =
        126 * (p.coeff 9 / h ^ 9) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 5 hh]
    have hle : (5 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 5 = 126 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h8_5 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 5 =
        -56 * (p.coeff 8 / h ^ 8) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 5 hh]
    have hle : (5 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 5 = 56 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]
    ring
  have h7_5 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 5 =
        21 * (p.coeff 7 / h ^ 7) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 5 hh]
    have hle : (5 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 5 = 21 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h6_5 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 5 =
        -6 * (p.coeff 6 / h ^ 6) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 5 hh]
    have hle : (5 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 5 = 6 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
  have h5_5 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 5 =
        p.coeff 5 / h ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 5 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    h10_5, h9_5, h8_5, h7_5, h6_5, h5_5, hlow 5 (by omega)]
  ring

end AffineDecic610Fifth

/-! ## Local scalar identities at a simple root -/

section FifthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The fourth-face jet reduces `M`, `T`, `U`, and `V` to a finite scalar
system in `(w, p₄, s, u₇)`.  That system forces all four scalars to
vanish. -/
theorem fifthFace_rootScalars_vanish610
    (w a4 s u7 : F)
    (hM : (18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u7 - (864 : F) * w * s + (720 : F) * w * a4 +
        (520 : F) * w ^ 3 = 0)
    (hU : -(576 : F) * a4 * s + (720 : F) * a4 ^ 2 -
        (504 : F) * w * u7 + (576 : F) * w ^ 2 * s -
        (360 : F) * w ^ 4 = 0)
    (hV : -(190080 : F) * a4 ^ 2 * w + (228096 : F) * a4 * s * w -
        (108864 : F) * a4 * u7 - (89760 : F) * a4 * w ^ 3 -
        (107712 : F) * s * w ^ 3 + (99792 : F) * u7 * w ^ 2 +
        (68816 : F) * w ^ 5 = 0) :
    w = 0 ∧ a4 = 0 ∧ s = 0 ∧ u7 = 0 := by
  have hQ :
      (27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4 = 0 :=
    fourthFace_rootQuartic_610 w a4 s u7 hM hT hU
  have hidV :
      -(190080 : F) * a4 ^ 2 * w + (228096 : F) * a4 * s * w -
            (108864 : F) * a4 * u7 - (89760 : F) * a4 * w ^ 3 -
            (107712 : F) * s * w ^ 3 + (99792 : F) * u7 * w ^ 2 +
            (68816 : F) * w ^ 5 -
          (4608 : F) * a4 * w *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) -
          (1408 : F) * w ^ 3 *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) +
          (168 : F) * a4 *
            ((648 : F) * u7 - (864 : F) * w * s +
              (720 : F) * w * a4 + (520 : F) * w ^ 3) -
          (154 : F) * w ^ 2 *
            ((648 : F) * u7 - (864 : F) * w * s +
              (720 : F) * w * a4 + (520 : F) * w ^ 3) =
        (2560 : F) * w *
            ((27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4) +
          (128 : F) * w ^ 3 * ((2 : F) * w ^ 2 - (15 : F) * a4) := by
    ring
  have hVred :
      (2560 : F) * w *
            ((27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4) +
          (128 : F) * w ^ 3 * ((2 : F) * w ^ 2 - (15 : F) * a4) = 0 := by
    rw [← hidV]
    linear_combination hV - (4608 : F) * a4 * w * hM -
      (1408 : F) * w ^ 3 * hM + (168 : F) * a4 * hT -
      (154 : F) * w ^ 2 * hT
  have hlin : (128 : F) * w ^ 3 * ((2 : F) * w ^ 2 - (15 : F) * a4) = 0 := by
    linear_combination hVred - (2560 : F) * w * hQ
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hprod : w ^ 3 * ((2 : F) * w ^ 2 - (15 : F) * a4) = 0 := by
    have hscale :
        (128 : F) * (w ^ 3 * ((2 : F) * w ^ 2 - (15 : F) * a4)) = 0 := by
      linear_combination hlin
    exact (mul_eq_zero.mp hscale).resolve_left h128
  have hidQL :
      (225 : F) * ((27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4) -
          ((405 : F) * a4 - (81 : F) * w ^ 2) *
            ((15 : F) * a4 - (2 : F) * w ^ 2) =
        (63 : F) * w ^ 4 := by
    ring
  have hw0a40 : w = 0 ∧ a4 = 0 := by
    rcases mul_eq_zero.mp hprod with hw3 | hface
    · have hw0 : w = 0 := by
        have hcube : w * (w * w) = w ^ 3 := by ring
        have hprod' : w * (w * w) = 0 := by
          rw [hcube, hw3]
        rcases mul_eq_zero.mp hprod' with hw | hsq
        · exact hw
        · exact (mul_eq_zero.mp hsq).elim id id
      have ha40 : a4 = 0 := by
        have h27 : (27 : F) ≠ 0 := by norm_num
        have : (27 : F) * a4 ^ 2 = 0 := by
          simpa [hw0] using hQ
        have ha2 : a4 ^ 2 = 0 :=
          (mul_eq_zero.mp this).resolve_left h27
        exact sq_eq_zero_iff.mp ha2
      exact ⟨hw0, ha40⟩
    · have hL : (15 : F) * a4 - (2 : F) * w ^ 2 = 0 := by
        linear_combination -hface
      have hw4 : (63 : F) * w ^ 4 = 0 := by
        rw [← hidQL]
        linear_combination (225 : F) * hQ -
          ((405 : F) * a4 - (81 : F) * w ^ 2) * hL
      have h63 : (63 : F) ≠ 0 := by norm_num
      have hw40 : w ^ 4 = 0 :=
        (mul_eq_zero.mp hw4).resolve_left h63
      have hw0 : w = 0 := by
        have hsq : (w ^ 2) ^ 2 = 0 := by
          convert hw40 using 1
          ring
        exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hsq)
      have ha40 : a4 = 0 := by
        have h15 : (15 : F) ≠ 0 := by norm_num
        have : (15 : F) * a4 = 0 := by
          simpa [hw0] using hL
        exact (mul_eq_zero.mp this).resolve_left h15
      exact ⟨hw0, ha40⟩
  have hs0 : s = 0 := by
    have h18 : (18 : F) ≠ 0 := by norm_num
    have : (18 : F) * s = 0 := by
      rw [hw0a40.1, hw0a40.2] at hM
      linear_combination hM
    exact (mul_eq_zero.mp this).resolve_left h18
  have hu0 : u7 = 0 := by
    have h648 : (648 : F) ≠ 0 := by norm_num
    have : (648 : F) * u7 = 0 := by
      rw [hw0a40.1, hw0a40.2] at hT
      linear_combination hT
    exact (mul_eq_zero.mp this).resolve_left h648
  exact ⟨hw0a40.1, hw0a40.2, hs0, hu0⟩

end FifthFaceScalars610

/-! ## Source-facing fifth-face packet -/

section NonzeroFifthFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The fourth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²⁵`. -/
theorem nonzeroFace610_fifthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eps : k,
      localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) lambda =
        Polynomial.C eps * h0 ^ 25 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
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
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
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
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
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
  have hdelta0deriv :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  obtain ⟨eps0, heps0⟩ :
      ∃ a : k,
        deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
            (g.coeff 5) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hdelta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda) =
        (93312 : RatFunc k) * hRF ^ 25 *
          deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
            (g.coeff 5) := by
    have hF := fifthDefect_eq_clearedDelta610 hRF a5 a4 a3 a2 a1 b9 b8 b7
      b6 b5 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedFifthDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, b8,
      b7, b6, b5, deltaResidual610, alphaResidual610, betaResidual610, hf4,
      hf3, hf2, hf1, hg5, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (93312 * eps0) * h0 ^ 25) := by
    rw [hclear, heps0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨93312 * eps0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading sextic coefficient to order four, the next sextic coefficient
to order one, the first unused decic coefficient to order five, `q₇`
to order two, and `q₉` to order eight. -/
theorem nonzeroFace610_linearRoot_fifthInitialPacket
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
    h0 ^ 4 ∣ p.coeff 5 ∧ h0 ∣ p.coeff 4 ∧
      h0 ^ 5 ∣ q.coeff 8 ∧ h0 ^ 2 ∣ q.coeff 7 ∧
      h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace610_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨hp5pow, hq8pow, hq7div, _hq9pow, _hquart⟩ :=
    nonzeroFace610_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
  obtain ⟨w, hw⟩ := hp5pow
  obtain ⟨s, hs⟩ := hq8pow
  obtain ⟨u7, hu7⟩ := hq7div
  have hM0 :
      (18 : k[X]) * s - (30 : k[X]) * p.coeff 4 -
          (10 : k[X]) * w ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 2 =
        Polynomial.C alpha * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 *
            ((18 : k[X]) * s - (30 : k[X]) * p.coeff 4 -
                (10 : k[X]) * w ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * w * h0 ^ 2) =
          localClearedSecondDefect610 h0 (p.coeff 5) (p.coeff 4)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect610, hw, hs]
        ring
      _ = Polynomial.C alpha * h0 ^ 10 := hM
      _ = h0 ^ 6 * (Polynomial.C alpha * h0 ^ 4) := by ring
  have hT0 :
      (520 : k[X]) * w ^ 3 - (864 : k[X]) * w * s +
          (720 : k[X]) * p.coeff 4 * w + (648 : k[X]) * u7 -
        (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 2 +
          (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 2 -
        (1080 : k[X]) * p.coeff 3 * h0 ^ 3 =
        Polynomial.C gamma * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
    calc
      h0 ^ 9 *
            ((520 : k[X]) * w ^ 3 - (864 : k[X]) * w * s +
                (720 : k[X]) * p.coeff 4 * w + (648 : k[X]) * u7 -
              (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 2 +
                (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 2 -
              (1080 : k[X]) * p.coeff 3 * h0 ^ 3) =
          localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect610, hw, hs, hu7]
        ring
      _ = Polynomial.C gamma * h0 ^ 15 := hT
      _ = h0 ^ 9 * (Polynomial.C gamma * h0 ^ 6) := by ring
  have hU0 :
      -(360 : k[X]) * w ^ 4 + (576 : k[X]) * w ^ 2 * s -
          (576 : k[X]) * p.coeff 4 * s - (504 : k[X]) * w * u7 +
        (720 : k[X]) * p.coeff 4 ^ 2 +
          (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 2 -
        (432 : k[X]) * Polynomial.C lambda * w * p.coeff 4 * h0 ^ 2 +
          (360 : k[X]) * w * p.coeff 3 * h0 ^ 3 +
        (432 : k[X]) * q.coeff 6 * h0 ^ 2 +
          (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 5 -
        (720 : k[X]) * p.coeff 2 * h0 ^ 6 =
        Polynomial.C delta * h0 ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
    calc
      h0 ^ 12 *
            (-(360 : k[X]) * w ^ 4 + (576 : k[X]) * w ^ 2 * s -
                (576 : k[X]) * p.coeff 4 * s - (504 : k[X]) * w * u7 +
              (720 : k[X]) * p.coeff 4 ^ 2 +
                (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 2 -
              (432 : k[X]) * Polynomial.C lambda * w * p.coeff 4 *
                  h0 ^ 2 +
                (360 : k[X]) * w * p.coeff 3 * h0 ^ 3 +
              (432 : k[X]) * q.coeff 6 * h0 ^ 2 +
                (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 5 -
              (720 : k[X]) * p.coeff 2 * h0 ^ 6) =
          localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect610, hw, hs, hu7]
        ring
      _ = Polynomial.C delta * h0 ^ 20 := hU
      _ = h0 ^ 12 * (Polynomial.C delta * h0 ^ 8) := by ring
  have hV0 :
      -(190080 : k[X]) * p.coeff 4 ^ 2 * w +
            (228096 : k[X]) * p.coeff 4 * s * w -
          (108864 : k[X]) * p.coeff 4 * u7 -
            (89760 : k[X]) * p.coeff 4 * w ^ 3 -
          (107712 : k[X]) * s * w ^ 3 + (99792 : k[X]) * u7 * w ^ 2 +
            (68816 : k[X]) * w ^ 5 +
          (-(42768 : k[X]) * Polynomial.C lambda * p.coeff 4 ^ 2 +
                (121176 : k[X]) * Polynomial.C lambda * p.coeff 4 *
                    w ^ 2 -
              (93312 : k[X]) * q.coeff 6 * w -
                (38709 : k[X]) * Polynomial.C lambda * w ^ 4) * h0 ^ 2 +
            ((285120 : k[X]) * p.coeff 3 * p.coeff 4 -
                  (124416 : k[X]) * p.coeff 3 * s +
                (23760 : k[X]) * p.coeff 3 * w ^ 2) * h0 ^ 3 +
          (-(85536 : k[X]) * Polynomial.C lambda * p.coeff 3 * w +
                (93312 : k[X]) * q.coeff 5) * h0 ^ 5 +
            (51840 : k[X]) * p.coeff 2 * w * h0 ^ 6 +
          (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 8 -
            (155520 : k[X]) * p.coeff 1 * h0 ^ 9 =
        Polynomial.C eps * h0 ^ 10 := by
    apply mul_left_cancel₀ (pow_ne_zero 15 hh0)
    calc
      h0 ^ 15 *
            (-(190080 : k[X]) * p.coeff 4 ^ 2 * w +
                  (228096 : k[X]) * p.coeff 4 * s * w -
                (108864 : k[X]) * p.coeff 4 * u7 -
                  (89760 : k[X]) * p.coeff 4 * w ^ 3 -
                (107712 : k[X]) * s * w ^ 3 +
                  (99792 : k[X]) * u7 * w ^ 2 +
                (68816 : k[X]) * w ^ 5 +
                  (-(42768 : k[X]) * Polynomial.C lambda *
                          p.coeff 4 ^ 2 +
                        (121176 : k[X]) * Polynomial.C lambda *
                            p.coeff 4 * w ^ 2 -
                      (93312 : k[X]) * q.coeff 6 * w -
                        (38709 : k[X]) * Polynomial.C lambda * w ^ 4) *
                      h0 ^ 2 +
                    ((285120 : k[X]) * p.coeff 3 * p.coeff 4 -
                          (124416 : k[X]) * p.coeff 3 * s +
                        (23760 : k[X]) * p.coeff 3 * w ^ 2) * h0 ^ 3 +
                  (-(85536 : k[X]) * Polynomial.C lambda * p.coeff 3 *
                          w +
                        (93312 : k[X]) * q.coeff 5) * h0 ^ 5 +
                    (51840 : k[X]) * p.coeff 2 * w * h0 ^ 6 +
                  (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                      h0 ^ 8 -
                    (155520 : k[X]) * p.coeff 1 * h0 ^ 9) =
          localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda := by
        simp only [localClearedFifthDefect610, hw, hs, hu7]
        ring
      _ = Polynomial.C eps * h0 ^ 25 := hVrel
      _ = h0 ^ 15 * (Polynomial.C eps * h0 ^ 10) := by ring
  have hMroot : (18 : k) * s.eval a - (30 : k) * (p.coeff 4).eval a -
      (10 : k) * (w.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (648 : k) * u7.eval a -
      (864 : k) * w.eval a * s.eval a +
        (720 : k) * w.eval a * (p.coeff 4).eval a +
      (520 : k) * (w.eval a) ^ 3 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    have hraw : (520 : k) * (w.eval a) ^ 3 -
        (864 : k) * w.eval a * s.eval a +
          (720 : k) * (p.coeff 4).eval a * w.eval a +
        (648 : k) * u7.eval a = 0 := by
      simpa [hroot] using heval
    linear_combination hraw
  have hUroot : -(576 : k) * (p.coeff 4).eval a * s.eval a +
      (720 : k) * ((p.coeff 4).eval a) ^ 2 -
        (504 : k) * w.eval a * u7.eval a +
      (576 : k) * (w.eval a) ^ 2 * s.eval a -
        (360 : k) * (w.eval a) ^ 4 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    have hraw : -(360 : k) * (w.eval a) ^ 4 +
        (576 : k) * (w.eval a) ^ 2 * s.eval a -
          (576 : k) * (p.coeff 4).eval a * s.eval a -
        (504 : k) * w.eval a * u7.eval a +
          (720 : k) * ((p.coeff 4).eval a) ^ 2 = 0 := by
      simpa [hroot] using heval
    linear_combination hraw
  have hVroot : -(190080 : k) * ((p.coeff 4).eval a) ^ 2 * w.eval a +
      (228096 : k) * (p.coeff 4).eval a * s.eval a * w.eval a -
        (108864 : k) * (p.coeff 4).eval a * u7.eval a -
          (89760 : k) * (p.coeff 4).eval a * (w.eval a) ^ 3 -
        (107712 : k) * s.eval a * (w.eval a) ^ 3 +
          (99792 : k) * u7.eval a * (w.eval a) ^ 2 +
        (68816 : k) * (w.eval a) ^ 5 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hV0
    simpa [hroot] using heval
  obtain ⟨hw0, ha40, hs0, hu0⟩ :=
    fifthFace_rootScalars_vanish610 (w.eval a) ((p.coeff 4).eval a)
      (s.eval a) (u7.eval a) hMroot hTroot hUroot hVroot
  have hw_div : h0 ∣ w :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w a hh0degree hroot hw0
  have ha4_div : h0 ∣ p.coeff 4 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 4) a
      hh0degree hroot ha40
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s a hh0degree hroot hs0
  have hu7_div : h0 ∣ u7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u7 a hh0degree hroot hu0
  have hp5pow4 : h0 ^ 4 ∣ p.coeff 5 := by
    obtain ⟨w1, hw1⟩ := hw_div
    refine ⟨w1, ?_⟩
    rw [hw, hw1]
    ring
  have hq8pow5 : h0 ^ 5 ∣ q.coeff 8 := by
    obtain ⟨s1, hs1⟩ := hs_div
    refine ⟨s1, ?_⟩
    rw [hs, hs1]
    ring
  have hq7pow2 : h0 ^ 2 ∣ q.coeff 7 := by
    obtain ⟨u8, hu8⟩ := hu7_div
    refine ⟨u8, ?_⟩
    rw [hu7, hu8]
    ring
  have hq9pow8 : h0 ^ 8 ∣ q.coeff 9 := by
    have h3 : (3 : k) ≠ 0 := by norm_num
    obtain ⟨w1, hw1⟩ := hw_div
    have hp5w1 : p.coeff 5 = h0 ^ 4 * w1 := by
      rw [hw, hw1]
      ring
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
          h0 ^ 8 * ((5 : k[X]) * w1 - Polynomial.C lambda * h0) := by
      rw [hN', hp5w1]
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
        ((5 : k[X]) * w1 - Polynomial.C lambda * h0), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp5pow4, ha4_div, hq8pow5, hq7pow2, hq9pow8⟩

/-- Source-facing fifth integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_fifthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eps : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFifthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda =
          Polynomial.C eps * h0 ^ 25 := by
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
  obtain ⟨eps, hV⟩ :=
    nonzeroFace610_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, eps, hh0, hlambda, hh0degree, hH, hN', hV⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the fifth-face jet `h⁴ ∣ p₅`, `h ∣ p₄`, `h⁵ ∣ q₈`,
`h² ∣ q₇`, and `h⁸ ∣ q₉`. -/
theorem normalized610ScaleTwo_nonzeroFace_fifthInitialPacket
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
        h0 ^ 4 ∣ p.coeff 5 ∧ h0 ∣ p.coeff 4 ∧
        h0 ^ 5 ∣ q.coeff 8 ∧ h0 ^ 2 ∣ q.coeff 7 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
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
  obtain ⟨hp5, hp4, hq8, hq7, hq9⟩ :=
    nonzeroFace610_linearRoot_fifthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hp4, hq8,
    hq7, hq9, hN'⟩

end NonzeroFifthFace610

#print axioms fifthCoefficientJacobianRow_610
#print axioms differentialJacobian_coeff_10_monicSexticDecic
#print axioms fifthDefect_eq_clearedDelta610
#print axioms nonzeroFace610_fifthDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_fifthInitialPacket
#print axioms normalized610ScaleTwo_nonzeroFace_fifthDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_fifthInitialPacket

end Max11DegreeRoutes
