import LowScale610ScaleTwoThirdFace

/-! # Scale-two fourth face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the third face supplies the degree-`12` integral
`Q - (5/3) B - (3/2) L A` and the local jet `h³ ∣ p₅`, `h⁴ ∣ q₈`,
`h ∣ q₇`, `h⁷ ∣ q₉`.  The next Keller coefficient is the degree-`11`
Jacobian row.  After the same sextic depression that kills `z⁵`, that
row is `10 C' + 9 L B' + 8 P A' - 4 A P' - 6 R' = 0`.  The resulting
first integral clears to a polynomial defect `U` of weight twenty.

Evaluating the second, third, and fourth defects together at the root
of `h` does not force a further individual vanishing.  It does force
the quartic relation `27 p₄(a)² - 9 w(a)² p₄(a) + w(a)⁴ = 0` on the
jets `p₅ = w h³` and `p₄`, equivalently
`h¹³ ∣ p₅⁴ - 9 p₅² p₄ h⁶ + 27 p₄² h¹²`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z²`/`z⁶` defect after the degree-`12` integral. -/
theorem fourthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 10).derivative) =
      0 := by
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
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC7, hC8, hC9, hC10, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Sextic `z²` and decic `z⁶` coordinates -/

section Depression610Fourth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed sextic `z²` coefficient. -/
abbrev depressedC610 (h r a5 a4 a3 a2 : F) : F :=
  depressedC68 h r a5 a4 a3 a2

/-- Depressed decic `z⁶` coefficient. -/
def depressedR610 (h r b9 b8 b7 b6 : F) : F :=
  210 * r ^ 4 - 84 * (b9 / h ^ 9) * r ^ 3 +
    28 * (b8 / h ^ 8) * r ^ 2 - 7 * (b7 / h ^ 7) * r + b6 / h ^ 6

/-- First residual of the degree-`11` row.  Equivalent to
`R - (5/3) C - (3/2) L B - (4/3) α A - (5/9) A²` on the second-face
integral `α = P - (5/3) A`. -/
def gammaResidual610 (L A B C0 P R : F) : F :=
  R - (5 / 3 : F) * C0 - (3 / 2 : F) * L * B -
    (4 / 3 : F) * P * A + (5 / 3 : F) * A ^ 2

/-- Polynomial numerator of `432 h²⁰ γ` on the ninth-power face. -/
def localClearedFourthDefect610
    (h a5 a4 a3 a2 b8 b7 b6 : F[X]) (lambda : F) : F[X] :=
  -(360 : F[X]) * a5 ^ 4 +
    (576 : F[X]) * a5 ^ 2 * b8 * h ^ 2 +
    (216 : F[X]) * Polynomial.C lambda * a5 ^ 3 * h ^ 5 -
    (576 : F[X]) * a4 * b8 * h ^ 8 -
    (504 : F[X]) * a5 * b7 * h ^ 8 -
    (432 : F[X]) * Polynomial.C lambda * a5 * a4 * h ^ 11 +
    (720 : F[X]) * a4 ^ 2 * h ^ 12 +
    (360 : F[X]) * a5 * a3 * h ^ 12 +
    (432 : F[X]) * b6 * h ^ 14 +
    (216 : F[X]) * Polynomial.C lambda * a3 * h ^ 17 -
    (720 : F[X]) * a2 * h ^ 18

theorem coeff_depressedSextic68_two
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 2 = C0 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the sextic `z²` coordinate. -/
theorem depressedC610_eq_cleared
    (h a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
      (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
          24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
        (144 * h ^ 20) := by
  simp only [depressedC610, depressedC68, sexticDepressionR610,
    sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁸` coordinate on the
ninth-power face. -/
theorem depressedP610_eq_cleared_ninthPower
    (h a5 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
      (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
        (4 * h ^ 10) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedP610, depressedP810, sexticDepressionR610,
    sexticDepressionR68]
  have hrewrite :
      45 * (a5 / (6 * h ^ 5)) ^ 2 -
          9 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) + b8 / h ^ 8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) := by
    field_simp [hh, h6, hh4, hh5, hh8pow, hh9, hh10, h4]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      have h3 : (3 : F) ≠ 0 := by norm_num
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, hh4, hh5, hh8pow, hh9, hh10, h4]
    ring
  exact hrewrite

/-- Exact denominator clearing for the decic `z⁶` coordinate on the
ninth-power face. -/
theorem depressedR610_eq_cleared
    (h a5 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
      (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
          336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
          432 * b6 * h ^ 14) /
        (432 * h ^ 20) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedR610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      210 * (a5 / (6 * h ^ 5)) ^ 4 -
          84 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 3 +
        28 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 2 -
          7 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) + b6 / h ^ 6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) := by
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh20, h432]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh20, h432]
    ring
  exact hrewrite

set_option maxHeartbeats 4000000 in
/-- Clearing the first integral
`R - (5/3) C - (3/2) L B - (4/3) α A - (5/9) A²` against `h²⁰` on the
ninth-power face. -/
theorem fourthDefect_eq_clearedGamma610
    (h a5 a4 a3 a2 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (432 : F) * h ^ 20 *
        gammaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6) =
      -(360 : F) * a5 ^ 4 + (576 : F) * a5 ^ 2 * b8 * h ^ 2 +
        (216 : F) * lambda * a5 ^ 3 * h ^ 5 -
        (576 : F) * a4 * b8 * h ^ 8 - (504 : F) * a5 * b7 * h ^ 8 -
        (432 : F) * lambda * a5 * a4 * h ^ 11 +
        (720 : F) * a4 ^ 2 * h ^ 12 + (360 : F) * a5 * a3 * h ^ 12 +
        (432 : F) * b6 * h ^ 14 + (216 : F) * lambda * a3 * h ^ 17 -
        (720 : F) * a2 * h ^ 18 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
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
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  have h432R :
      (432 : F) * h ^ 20 *
          depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        -(210 : F) * a5 ^ 4 + (56 : F) * lambda * a5 ^ 3 * h ^ 5 +
          (336 : F) * a5 ^ 2 * b8 * h ^ 2 -
          (504 : F) * a5 * b7 * h ^ 8 + (432 : F) * b6 * h ^ 14 := by
    rw [hR]
    field_simp [hh, h432, hh20]
    try ring
  have h720C :
      (720 : F) * h ^ 20 *
          depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (720 : F) * a2 * h ^ 18 - (360 : F) * a3 * a5 * h ^ 12 +
          (120 : F) * a4 * a5 ^ 2 * h ^ 6 - (25 : F) * a5 ^ 4 := by
    rw [hC]
    field_simp [hh, h144, hh20]
    ring
  have h216B :
      (216 : F) * lambda * h ^ 20 *
          depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (216 : F) * lambda * a3 * h ^ 17 -
          (144 : F) * lambda * a4 * a5 * h ^ 11 +
          (40 : F) * lambda * a5 ^ 3 * h ^ 5 := by
    rw [hB]
    field_simp [hh, h54, hh15, hh20]
    ring
  have h12A :
      (12 : F) * h ^ 10 *
          depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2 := by
    rw [hA]
    field_simp [hh, h12, hh10]
    try ring
  have h4P :
      (4 : F) * h ^ 10 *
          depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        -(5 : F) * a5 ^ 2 + (2 : F) * lambda * a5 * h ^ 5 +
          (4 : F) * b8 * h ^ 2 := by
    rw [hP]
    field_simp [hh, h4, hh10]
    try ring
  have h576AP :
      (576 : F) * h ^ 20 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
            depressedP610 h (sexticDepressionR610 h a5) b9 b8) =
        (12 : F) *
          ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) *
            (-(5 : F) * a5 ^ 2 + (2 : F) * lambda * a5 * h ^ 5 +
              (4 : F) * b8 * h ^ 2) := by
    have hscale :
        (576 : F) * h ^ 20 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedP610 h (sexticDepressionR610 h a5) b9 b8) =
          (12 : F) *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5 a4) *
              ((4 : F) * h ^ 10 *
                depressedP610 h (sexticDepressionR610 h a5) b9 b8) := by
      ring
    rw [hscale, h12A, h4P]
  have h720A2 :
      (720 : F) * h ^ 20 *
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 =
        (5 : F) * ((12 : F) * a4 * h ^ 6 - (5 : F) * a5 ^ 2) ^ 2 := by
    have hscale :
        (720 : F) * h ^ 20 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 =
          (5 : F) *
            ((12 : F) * h ^ 10 *
                depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 := by
      field_simp [hh, h12, hh10, hh20]
      ring
    rw [hscale, h12A]
  have hdiff :
      (432 : F) * h ^ 20 *
          gammaResidual610
            (depressedL610 h (sexticDepressionR610 h a5) b9)
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
            (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
            (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
            (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
            (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6) =
        (432 : F) * h ^ 20 *
            depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 -
          (720 : F) * h ^ 20 *
            depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 +
          (216 : F) * lambda * h ^ 20 *
            depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 -
          (576 : F) * h ^ 20 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4 *
              depressedP610 h (sexticDepressionR610 h a5) b9 b8) +
          (720 : F) * h ^ 20 *
            (depressedA610 h (sexticDepressionR610 h a5) a5 a4) ^ 2 := by
    simp only [gammaResidual610, hL]
    field_simp [h2, h3]
    ring
  rw [hdiff, h432R, h720C, h216B, h576AP, h720A2]
  ring

end Depression610Fourth

/-! ## Degree-`11` depressed Jacobian coefficient -/

section DepressedRow610Fourth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`11` Jacobian coefficient is
exactly `10 C' + 9 L B' + 8 P A' - 4 A P' - 6 R'`. -/
theorem differentialJacobian_coeff_11_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 11 =
      (10 : F) * d (f.coeff 2) + (9 : F) * g.coeff 9 * d (f.coeff 3) +
        (8 : F) * g.coeff 8 * d (f.coeff 4) -
          (4 : F) * f.coeff 4 * d (g.coeff 8) -
          (6 : F) * d (g.coeff 6) := by
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
  have hmem29 : ((2, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem38 : ((3, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem47 : ((4, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem56 : ((5, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 11 =
        (10 : F) * d (f.coeff 2) +
          (9 : F) * g.coeff 9 * d (f.coeff 3) +
          (8 : F) * g.coeff 8 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne23 : ((2, 9) : ℕ × ℕ) ≠ (3, 8) := by decide
    have hne24 : ((2, 9) : ℕ × ℕ) ≠ (4, 7) := by decide
    have hne34 : ((3, 8) : ℕ × ℕ) ≠ (4, 7) := by decide
    have hsubset : ({(2, 9), (3, 8), (4, 7)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (11 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem29
      · subst b
        exact hmem38
      · subst b
        exact hmem47
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(2, 9), (3, 8), (4, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne29 : b ≠ (2, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne38 : b ≠ (3, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne47 : b ≠ (4, 7) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne29
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne38
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne47
          ext
          · exact h4
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(2, 9), (3, 8), (4, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 2 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 7 := by
      rw [Finset.sum_insert (by simp [hne23, hne24]),
        Finset.sum_insert (by simp [hne34]), Finset.sum_singleton]
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
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder9, hder8, hder7]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 11 =
        (4 : F) * f.coeff 4 * d (g.coeff 8) +
          (6 : F) * d (g.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne : ((3, 8) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hsubset : ({(3, 8), (5, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (11 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem38
      · subst b
        exact hmem56
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(3, 8), (5, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne38 : b ≠ (3, 8) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne56 : b ≠ (5, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne38
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne56
            ext
            · exact h5
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(3, 8), (5, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 3 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 6 := by
      rw [Finset.sum_pair hne]
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem gammaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 P R : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hrow : (10 : F) * d C0 + (9 : F) * L * d B +
        (8 : F) * P * d A - (4 : F) * A * d P -
        (6 : F) * d R = 0) :
    d (gammaResidual610 L A B C0 P R) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have hPderiv : d P = (5 / 3 : F) * d A := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hP0 : d P - (5 / 3 : F) * d A = 0 := by
    linear_combination hPderiv
  have hgamma :
      gammaResidual610 L A B C0 P R =
        R - (5 / 3 : F) * C0 - (3 / 2 : F) * L * B -
          (4 / 3 : F) * P * A + (5 / 3 : F) * (A * A) := by
    simp only [gammaResidual610, pow_two]
  rw [hgamma]
  simp [map_sub, Derivation.leibniz, h53, h32, h43, hL, zero_mul, add_zero,
    mul_zero, hsq]
  linear_combination (-1 / 6 : F) * hrow + (-2 : F) * A * hP0

end DepressedRow610Fourth

/-! ## Affine depression of a degree-ten source, `z⁶` coefficient -/

section AffineDecic610Fourth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁶` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff6_610
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 6 =
      210 * r ^ 4 - 84 * (p.coeff 9 / h ^ 9) * r ^ 3 +
        28 * (p.coeff 8 / h ^ 8) * r ^ 2 -
        7 * (p.coeff 7 / h ^ 7) * r + p.coeff 6 / h ^ 6 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6
  have hplow : ∀ n, 6 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h6 | hlt6
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
                show n ≠ 7 by omega, show n ≠ 6 by omega]
  have hplowDeg : plow.natDegree ≤ 5 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H s : (RatFunc k)[X]) :
        (A + B + D + E + G + H).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s +
            H.comp s := by
      have h1 : (A + B + D + E + G + H).comp s =
          (A + B + D + E + G).comp s + H.comp s := add_comp
      have h2 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h3 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h4 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h5 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4, h5]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 6 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 5 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 5 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 6 ≤ n))
  have h10_6 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 6 =
        210 * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 6 hh]
    have hle : (6 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 6 = 210 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]
    ring
  have h9_6 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 6 =
        -84 * (p.coeff 9 / h ^ 9) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 6 hh]
    have hle : (6 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 6 = 84 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]
    ring
  have h8_6 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 6 =
        28 * (p.coeff 8 / h ^ 8) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 6 hh]
    have hle : (6 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 6 = 28 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h7_6 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 6 =
        -7 * (p.coeff 7 / h ^ 7) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 6 hh]
    have hle : (6 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 6 = 7 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
  have h6_6 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 6 =
        p.coeff 6 / h ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 6 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, h10_6,
    h9_6, h8_6, h7_6, h6_6, hlow 6 (by omega)]
  ring

end AffineDecic610Fourth

/-! ## Local scalar identity at a simple root -/

section FourthFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The third-face jet reduces `M`, `T`, and `U` to a finite scalar
system in `(w, p₄, s, u₇)`.  That system forces the quartic
`27 p₄² - 9 w² p₄ + w⁴ = 0` and does not force any individual
vanishing. -/
theorem fourthFace_rootQuartic_610
    (w a4 s u7 : F)
    (hM : (18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2 = 0)
    (hT : (648 : F) * u7 - (864 : F) * w * s + (720 : F) * w * a4 +
        (520 : F) * w ^ 3 = 0)
    (hU : -(576 : F) * a4 * s + (720 : F) * a4 ^ 2 -
        (504 : F) * w * u7 + (576 : F) * w ^ 2 * s -
        (360 : F) * w ^ 4 = 0) :
    (27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4 = 0 := by
  have hid :
      (9 : F) *
            (-(576 : F) * a4 * s + (720 : F) * a4 ^ 2 -
              (504 : F) * w * u7 + (576 : F) * w ^ 2 * s -
              (360 : F) * w ^ 4) +
          (288 : F) * a4 *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) +
        (7 : F) * w *
            ((648 : F) * u7 - (864 : F) * w * s +
              (720 : F) * w * a4 + (520 : F) * w ^ 3) +
          (48 : F) * w ^ 2 *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) =
        -(80 : F) *
          ((27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4) := by
    ring
  have hleft :
      (9 : F) *
            (-(576 : F) * a4 * s + (720 : F) * a4 ^ 2 -
              (504 : F) * w * u7 + (576 : F) * w ^ 2 * s -
              (360 : F) * w ^ 4) +
          (288 : F) * a4 *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) +
        (7 : F) * w *
            ((648 : F) * u7 - (864 : F) * w * s +
              (720 : F) * w * a4 + (520 : F) * w ^ 3) +
          (48 : F) * w ^ 2 *
            ((18 : F) * s - (30 : F) * a4 - (10 : F) * w ^ 2) = 0 := by
    linear_combination (9 : F) * hU + (288 : F) * a4 * hM +
      (7 : F) * w * hT + (48 : F) * w ^ 2 * hM
  have h80 : (80 : F) ≠ 0 := by norm_num
  have hneg :
      -(80 : F) *
          ((27 : F) * a4 ^ 2 - (9 : F) * w ^ 2 * a4 + w ^ 4) = 0 :=
    hid.symm.trans hleft
  exact (mul_eq_zero.mp (by linear_combination -hneg)).resolve_left h80

end FourthFaceScalars610

/-! ## Source-facing fourth-face packet -/

section NonzeroFourthFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The third sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²⁰`. -/
theorem nonzeroFace610_fourthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ delta : k,
      localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (q.coeff 8) (q.coeff 7) (q.coeff 6) lambda =
        Polynomial.C delta * h0 ^ 20 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
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
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
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
  have hf4 : f.coeff 4 = depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
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
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  obtain ⟨delta0, hdelta0⟩ :
      ∃ a : k,
        gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (g.coeff 8) (g.coeff 6) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hgamma0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        (432 : RatFunc k) * hRF ^ 20 *
          gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (g.coeff 8) (g.coeff 6) := by
    have hF := fourthDefect_eq_clearedGamma610 hRF a5 a4 a3 a2 b9 b8 b7 b6
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedFourthDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, b8,
      b7, b6, gammaResidual610, hf4, hf3, hf2, hg6, hg8', hg9L] using
      hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (432 * delta0) * h0 ^ 20) := by
    rw [hclear, hdelta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨432 * delta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the third-face jet together with the
degree-`11` defect forces the quartic divisibility
`h¹³ ∣ p₅⁴ - 9 p₅² p₄ h⁶ + 27 p₄² h¹²` at the degree-one root. -/
theorem nonzeroFace610_linearRoot_fourthInitialPacket
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
    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
      h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 ∧
      h0 ^ 13 ∣ (p.coeff 5) ^ 4 -
        (9 : k[X]) * (p.coeff 5) ^ 2 * p.coeff 4 * h0 ^ 6 +
        (27 : k[X]) * (p.coeff 4) ^ 2 * h0 ^ 12 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨hp5pow, hq8pow, hq7div, hq9pow⟩ :=
    nonzeroFace610_linearRoot_thirdInitialPacket p q H h0 j lambda a
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
  have hquart :
      (27 : k) * ((p.coeff 4).eval a) ^ 2 -
          (9 : k) * (w.eval a) ^ 2 * (p.coeff 4).eval a +
        (w.eval a) ^ 4 = 0 :=
    fourthFace_rootQuartic_610 (w.eval a) ((p.coeff 4).eval a)
      (s.eval a) (u7.eval a) hMroot hTroot hUroot
  have hform :
      (p.coeff 5) ^ 4 -
          (9 : k[X]) * (p.coeff 5) ^ 2 * p.coeff 4 * h0 ^ 6 +
        (27 : k[X]) * (p.coeff 4) ^ 2 * h0 ^ 12 =
        h0 ^ 12 *
          (w ^ 4 - (9 : k[X]) * w ^ 2 * p.coeff 4 +
            (27 : k[X]) * p.coeff 4 ^ 2) := by
    rw [hw]
    ring
  have hjet0 :
      (w ^ 4 - (9 : k[X]) * w ^ 2 * p.coeff 4 +
          (27 : k[X]) * p.coeff 4 ^ 2).eval a = 0 := by
    have heval :
        (w ^ 4 - (9 : k[X]) * w ^ 2 * p.coeff 4 +
            (27 : k[X]) * p.coeff 4 ^ 2).eval a =
          (w.eval a) ^ 4 - (9 : k) * (w.eval a) ^ 2 * (p.coeff 4).eval a +
            (27 : k) * ((p.coeff 4).eval a) ^ 2 := by
      simp [eval_pow]
    rw [heval]
    linear_combination hquart
  have hjetdiv : h0 ∣
      w ^ 4 - (9 : k[X]) * w ^ 2 * p.coeff 4 +
        (27 : k[X]) * p.coeff 4 ^ 2 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0
      (w ^ 4 - (9 : k[X]) * w ^ 2 * p.coeff 4 +
        (27 : k[X]) * p.coeff 4 ^ 2) a hh0degree hroot hjet0
  obtain ⟨rQ, hrQ⟩ := hjetdiv
  refine ⟨⟨w, hw⟩, ⟨s, hs⟩, ⟨u7, hu7⟩, hq9pow, ⟨rQ, ?_⟩⟩
  rw [hform, hrQ]
  ring

/-- Source-facing fourth integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_fourthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda delta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda =
          Polynomial.C delta * h0 ^ 20 := by
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
  obtain ⟨delta, hU⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, delta, hh0, hlambda, hh0degree, hH, hN', hU⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the third-face jet together with the quartic relation
`h¹³ ∣ p₅⁴ - 9 p₅² p₄ h⁶ + 27 p₄² h¹²`. -/
theorem normalized610ScaleTwo_nonzeroFace_fourthInitialPacket
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
        h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 8 ∧
        h0 ∣ q.coeff 7 ∧ h0 ^ 7 ∣ q.coeff 9 ∧
        h0 ^ 13 ∣ (p.coeff 5) ^ 4 -
          (9 : K[X]) * (p.coeff 5) ^ 2 * p.coeff 4 * h0 ^ 6 +
          (27 : K[X]) * (p.coeff 4) ^ 2 * h0 ^ 12 ∧
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
  obtain ⟨hp5, hq8, hq7, hq9, hquart⟩ :=
    nonzeroFace610_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hq8, hq7,
    hq9, hquart, hN'⟩

end NonzeroFourthFace610

#print axioms fourthCoefficientJacobianRow_610
#print axioms differentialJacobian_coeff_11_monicSexticDecic
#print axioms fourthDefect_eq_clearedGamma610
#print axioms nonzeroFace610_fourthDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_fourthInitialPacket
#print axioms normalized610ScaleTwo_nonzeroFace_fourthDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_fourthInitialPacket

end Max11DegreeRoutes
