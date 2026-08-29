import LowScale410ScaleTwoThirdFace

/-! # Scale-two fourth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the third face supplies the degree-`10` integral
`Q - (5/2) B - (9/4) L A` and the local jet `h ∣ p₃`, `h⁴ ∣ q₈`,
`h ∣ q₇`, `h⁷ ∣ q₉`.  The next Keller coefficient is the degree-`9`
Jacobian row.  After the same quartic depression that kills `z³`, that
row is `10 C' + 9 L B' + 8 P A' - 2 A P' - 4 R' = 0`.  The resulting
first integral clears to a polynomial defect `U` of weight fourteen.

Evaluating the second, third, and fourth defects together at the root
of `h` forces the finite initial jet `h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`,
`h² ∣ q₆`, and `h⁸ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fourth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z⁰`/`z⁶` defect after the degree-`10` integral. -/
theorem fourthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 8).derivative +
        p.coeff 1 * (q.coeff 9).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 9) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (9 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 9 :
      Finset (ℕ × ℕ)) =
      ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3),
        (7, 2), (8, 1), (9, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC6, hC7, hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z⁶` coordinates -/

section Depression410Fourth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed quartic constant term. -/
abbrev depressedC410 (h r a3 a2 a1 a0 : F) : F :=
  depressedC46 h r a3 a2 a1 a0

/-- Depressed decic `z⁶` coefficient. -/
def depressedR410 (h r b9 b8 b7 b6 : F) : F :=
  210 * r ^ 4 - 84 * (b9 / h ^ 9) * r ^ 3 +
    28 * (b8 / h ^ 8) * r ^ 2 - 7 * (b7 / h ^ 7) * r + b6 / h ^ 6

/-- First residual of the degree-`9` row.  Equivalent to
`R - (5/2) C - (9/4) L B - 2 α A - (15/8) A²` on the second-face
integral `α = P - (5/2) A`. -/
def gammaResidual410 (L A B C0 P R : F) : F :=
  R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
    (2 : F) * P * A + (25 / 8 : F) * A ^ 2

/-- Polynomial numerator of `128 h¹⁴ γ` on the ninth-power face. -/
def localClearedFourthDefect410
    (h a3 a2 a1 a0 b8 b7 b6 : F[X]) (lambda : F) : F[X] :=
  -(525 : F[X]) * a3 ^ 4 * h ^ 2 +
    (210 : F[X]) * Polynomial.C lambda * a3 ^ 3 * h ^ 5 +
    (320 : F[X]) * a3 ^ 2 * b8 +
    (400 : F[X]) * a2 * a3 ^ 2 * h ^ 6 -
    (360 : F[X]) * Polynomial.C lambda * a2 * a3 * h ^ 9 -
    (224 : F[X]) * a3 * b7 * h ^ 4 -
    (256 : F[X]) * a2 * b8 * h ^ 4 +
    (80 : F[X]) * a1 * a3 * h ^ 10 +
    (400 : F[X]) * a2 ^ 2 * h ^ 10 +
    (144 : F[X]) * Polynomial.C lambda * a1 * h ^ 13 +
    (128 : F[X]) * b6 * h ^ 8 -
    (320 : F[X]) * a0 * h ^ 14

omit [CharZero F] in
theorem coeff_depressedQuartic46_zero
    (A B C0 : F) :
    (depressedQuartic46 A B C0).coeff 0 = C0 := by
  simp [depressedQuartic46, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the quartic constant. -/
theorem depressedC410_eq_cleared
    (h a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
      (256 * a0 * h ^ 12 - 64 * a1 * a3 * h ^ 8 +
          16 * a2 * a3 ^ 2 * h ^ 4 - 3 * a3 ^ 4) /
        (256 * h ^ 12) := by
  simp only [depressedC410, depressedC46, quarticDepressionR410,
    quarticDepressionR46]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁸` coordinate on the
ninth-power face. -/
theorem depressedP410_eq_cleared_ninthPower
    (h a3 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedP410 h (quarticDepressionR410 h a3) b9 b8 =
      (16 * b8 - 45 * a3 ^ 2 * h ^ 2 + 18 * lambda * a3 * h ^ 5) /
        (16 * h ^ 8) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedP410, depressedP810, quarticDepressionR410,
    quarticDepressionR46]
  have hrewrite :
      45 * (a3 / (4 * h ^ 3)) ^ 2 -
          9 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) + b8 / h ^ 8 =
        (16 * b8 - 45 * a3 ^ 2 * h ^ 2 + 18 * lambda * a3 * h ^ 5) /
          (16 * h ^ 8) := by
    field_simp [hh, h2, h4, hh3, hh6, hh8pow, hh9, h16]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh6, hh8pow, hh9, h16]
    ring
  exact hrewrite

/-- Exact denominator clearing for the decic `z⁶` coordinate on the
ninth-power face. -/
theorem depressedR410_eq_cleared
    (h a3 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 =
      (-315 * a3 ^ 4 * h ^ 2 + 84 * lambda * a3 ^ 3 * h ^ 5 +
          224 * a3 ^ 2 * b8 - 224 * a3 * b7 * h ^ 4 +
          128 * b6 * h ^ 8) /
        (128 * h ^ 14) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedR410, quarticDepressionR410, quarticDepressionR46]
  have hrewrite :
      210 * (a3 / (4 * h ^ 3)) ^ 4 -
          84 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 3 +
        28 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) ^ 2 -
          7 * (b7 / h ^ 7) * (a3 / (4 * h ^ 3)) + b6 / h ^ 6 =
        (-315 * a3 ^ 4 * h ^ 2 + 84 * lambda * a3 ^ 3 * h ^ 5 +
            224 * a3 ^ 2 * b8 - 224 * a3 * b7 * h ^ 4 +
            128 * b6 * h ^ 8) /
          (128 * h ^ 14) := by
    field_simp [hh, h2, h4, hh3, hh6, hh7, hh8pow, hh9, hh14, h128]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh6, hh7, hh8pow, hh9, hh14, h128]
    ring
  exact hrewrite

set_option maxHeartbeats 4000000 in
/-- Clearing the first integral
`R - (5/2) C - (9/4) L B - 2 P A + (25/8) A²` against `h¹⁴` on the
ninth-power face. -/
theorem fourthDefect_eq_clearedGamma410
    (h a3 a2 a1 a0 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (128 : F) * h ^ 14 *
        gammaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6) =
      -(525 : F) * a3 ^ 4 * h ^ 2 + (210 : F) * lambda * a3 ^ 3 * h ^ 5 +
        (320 : F) * a3 ^ 2 * b8 + (400 : F) * a2 * a3 ^ 2 * h ^ 6 -
        (360 : F) * lambda * a2 * a3 * h ^ 9 -
        (224 : F) * a3 * b7 * h ^ 4 - (256 : F) * a2 * b8 * h ^ 4 +
        (80 : F) * a1 * a3 * h ^ 10 + (400 : F) * a2 ^ 2 * h ^ 10 +
        (144 : F) * lambda * a1 * h ^ 13 + (128 : F) * b6 * h ^ 8 -
        (320 : F) * a0 * h ^ 14 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh12 : h ^ 12 ≠ 0 := pow_ne_zero 12 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hL :
      depressedL410 h (quarticDepressionR410 h a3) b9 = -lambda / 2 :=
    depressedL410_eq_of_ninthPower h a3 b9 lambda hh hN
  have hA :
      depressedA410 h (quarticDepressionR410 h a3) a3 a2 =
        (8 * a2 * h ^ 4 - 3 * a3 ^ 2) / (8 * h ^ 6) :=
    depressedA410_eq_cleared h a3 a2 hh
  have hB :
      depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
        (a3 ^ 3 - 4 * a2 * a3 * h ^ 4 + 8 * a1 * h ^ 8) /
          (8 * h ^ 9) :=
    depressedB410_eq_cleared h a3 a2 a1 hh
  have hC :
      depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
        (256 * a0 * h ^ 12 - 64 * a1 * a3 * h ^ 8 +
            16 * a2 * a3 ^ 2 * h ^ 4 - 3 * a3 ^ 4) /
          (256 * h ^ 12) :=
    depressedC410_eq_cleared h a3 a2 a1 a0 hh
  have hP :
      depressedP410 h (quarticDepressionR410 h a3) b9 b8 =
        (16 * b8 - 45 * a3 ^ 2 * h ^ 2 + 18 * lambda * a3 * h ^ 5) /
          (16 * h ^ 8) :=
    depressedP410_eq_cleared_ninthPower h a3 b9 b8 lambda hh hN
  have hR :
      depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 =
        (-315 * a3 ^ 4 * h ^ 2 + 84 * lambda * a3 ^ 3 * h ^ 5 +
            224 * a3 ^ 2 * b8 - 224 * a3 * b7 * h ^ 4 +
            128 * b6 * h ^ 8) /
          (128 * h ^ 14) :=
    depressedR410_eq_cleared h a3 b9 b8 b7 b6 lambda hh hN
  have h128R :
      (128 : F) * h ^ 14 *
          depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 =
        -(315 : F) * a3 ^ 4 * h ^ 2 + (84 : F) * lambda * a3 ^ 3 * h ^ 5 +
          (224 : F) * a3 ^ 2 * b8 - (224 : F) * a3 * b7 * h ^ 4 +
          (128 : F) * b6 * h ^ 8 := by
    rw [hR]
    field_simp [hh, h128, hh14]
    try ring
  have h8A :
      (8 : F) * h ^ 6 *
          depressedA410 h (quarticDepressionR410 h a3) a3 a2 =
        (8 : F) * a2 * h ^ 4 - (3 : F) * a3 ^ 2 := by
    rw [hA]
    field_simp [hh, h8, hh6]
    try ring
  have h8B :
      (8 : F) * h ^ 9 *
          depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
        a3 ^ 3 - (4 : F) * a2 * a3 * h ^ 4 + (8 : F) * a1 * h ^ 8 := by
    rw [hB]
    field_simp [hh, h8, hh9]
    try ring
  have h16P :
      (16 : F) * h ^ 8 *
          depressedP410 h (quarticDepressionR410 h a3) b9 b8 =
        (16 : F) * b8 - (45 : F) * a3 ^ 2 * h ^ 2 +
          (18 : F) * lambda * a3 * h ^ 5 := by
    rw [hP]
    field_simp [hh, h16, hh8pow]
    try ring
  have h256C :
      (256 : F) * h ^ 12 *
          depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
        (256 : F) * a0 * h ^ 12 - (64 : F) * a1 * a3 * h ^ 8 +
          (16 : F) * a2 * a3 ^ 2 * h ^ 4 - (3 : F) * a3 ^ 4 := by
    rw [hC]
    field_simp [hh, h256, hh12]
    try ring
  have h144B :
      (144 : F) * lambda * h ^ 14 *
          depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 =
        (18 : F) * lambda * h ^ 5 *
          ((8 : F) * h ^ 9 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) := by
    ring
  have h256PA :
      (256 : F) * h ^ 14 *
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
            depressedA410 h (quarticDepressionR410 h a3) a3 a2) =
        (2 : F) *
          ((16 : F) * h ^ 8 *
              depressedP410 h (quarticDepressionR410 h a3) b9 b8) *
            ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) := by
    ring
  have h400A2 :
      (400 : F) * h ^ 14 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^ 2 =
        (25 : F) / 4 *
          h ^ 2 *
            ((8 : F) * h ^ 6 *
                depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^ 2 := by
    field_simp [hh, h8, hh6, hh14, h4]
    ring
  have h320C :
      (320 : F) * h ^ 14 *
          depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
        (5 : F) / 4 * h ^ 2 *
          ((256 : F) * h ^ 12 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0) := by
    field_simp [hh, h256, hh12, hh14, h4]
    ring
  have hdiff :
      (128 : F) * h ^ 14 *
          gammaResidual410
            (depressedL410 h (quarticDepressionR410 h a3) b9)
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
            (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
            (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6) =
        (128 : F) * h ^ 14 *
            depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 -
          (320 : F) * h ^ 14 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 +
          (144 : F) * lambda * h ^ 14 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1 -
          (256 : F) * h ^ 14 *
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) +
          (400 : F) * h ^ 14 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^ 2 := by
    simp only [gammaResidual410, hL]
    field_simp [h2, h4]
    ring
  rw [hdiff, h128R, h320C, h144B, h8B, h256PA, h16P, h8A, h400A2, h8A,
    h256C]
  field_simp [h4]
  ring

end Depression410Fourth

/-! ## Degree-`9` depressed Jacobian coefficient -/

section DepressedRow410Fourth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`9` Jacobian coefficient is
exactly `10 C' + 9 L B' + 8 P A' - 2 A P' - 4 R'`. -/
theorem differentialJacobian_coeff_9_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 9 =
      (10 : F) * d (f.coeff 0) + (9 : F) * g.coeff 9 * d (f.coeff 1) +
        (8 : F) * g.coeff 8 * d (f.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 8) -
          (4 : F) * d (g.coeff 6) := by
  have hfd_high : ∀ n, 3 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf3]
    · have : 4 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq4 | hlt4
      · subst n
        simpa [hf4, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 4 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 4 < n + 1 := by omega
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
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 9 =
        (10 : F) * d (f.coeff 0) +
          (9 : F) * g.coeff 9 * d (f.coeff 1) +
          (8 : F) * g.coeff 8 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 9) : ℕ × ℕ) ≠ (1, 8) := by decide
    have hne02 : ((0, 9) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne12 : ((1, 8) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hsubset : ({(0, 9), (1, 8), (2, 7)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem09
      · subst b
        exact hmem18
      · subst b
        exact hmem27
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 9), (1, 8), (2, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne09 : b ≠ (0, 9) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne18 : b ≠ (1, 8) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne27 : b ≠ (2, 7) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
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
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 9), (1, 8), (2, 7)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 7 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
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
      (f.derivative * coefficientDeriv d g).coeff 9 =
        (2 : F) * f.coeff 2 * d (g.coeff 8) +
          (4 : F) * d (g.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne : ((1, 8) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hsubset : ({(1, 8), (3, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb
      · subst b
        exact hmem18
      · subst b
        exact hmem36
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(1, 8), (3, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne18 : b ≠ (1, 8) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne36 : b ≠ (3, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 4 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h2 : b.1 = 2
        · have hf2 : f.derivative.coeff b.1 = 0 := by
            rw [h2, Polynomial.coeff_derivative, hf3]
            simp
          simp [hf2]
        · have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne18
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne36
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 8), (3, 6)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 1 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 6 := by
      rw [Finset.sum_pair hne]
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder1, hder3]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem gammaResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P R : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hrow : (10 : F) * d C0 + (9 : F) * L * d B +
        (8 : F) * P * d A - (2 : F) * A * d P -
        (4 : F) * d R = 0) :
    d (gammaResidual410 L A B C0 P R) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have hP0 : d P - (5 / 2 : F) * d A = 0 := by
    have halpha' : d P - (5 / 2 : F) * d A = 0 := by
      simpa [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    try ring
  have htarget :
      d R - (5 / 2 : F) * d C0 - (9 / 4 : F) * L * d B -
          (2 : F) * A * d P - (2 : F) * P * d A +
          (25 / 4 : F) * A * d A = 0 := by
    linear_combination (-1 / 4 : F) * hrow + (-5 / 2 : F) * A * hP0
  have hgamma :
      gammaResidual410 L A B C0 P R =
        R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
          (2 : F) * P * A + (25 / 8 : F) * (A * A) := by
    simp only [gammaResidual410, pow_two]
  rw [hgamma]
  simp [map_sub, map_add, Derivation.leibniz, h2, h52, h94, h258, hL, hsq,
    zero_mul, add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Fourth

/-! ## Affine depression of a degree-ten source, `z⁶` coefficient -/

section AffineDecic410Fourth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁶` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff6_410
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

end AffineDecic410Fourth

/-! ## Local scalar identity at a simple root -/

section FourthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The third-face jet reduces `M`, `T`, and `U` to a finite scalar
system in `(t, s, u₇)`.  That system forces all three jets to vanish. -/
theorem fourthFace_rootScalars_vanish410
    (t s u7 : F)
    (hM : (8 : F) * s - (15 : F) * t ^ 2 = 0)
    (hT : (64 : F) * u7 - (128 : F) * s * t + (220 : F) * t ^ 3 = 0)
    (hU : (320 : F) * s * t ^ 2 - (525 : F) * t ^ 4 -
        (224 : F) * t * u7 = 0) :
    t = 0 ∧ s = 0 ∧ u7 = 0 := by
  have hid :
      (7 : F) * t *
            ((64 : F) * u7 - (128 : F) * s * t + (220 : F) * t ^ 3) +
          (2 : F) *
            ((320 : F) * s * t ^ 2 - (525 : F) * t ^ 4 -
              (224 : F) * t * u7) +
        (32 : F) * t ^ 2 * ((8 : F) * s - (15 : F) * t ^ 2) =
        (10 : F) * t ^ 4 := by
    ring
  have hleft :
      (7 : F) * t *
            ((64 : F) * u7 - (128 : F) * s * t + (220 : F) * t ^ 3) +
          (2 : F) *
            ((320 : F) * s * t ^ 2 - (525 : F) * t ^ 4 -
              (224 : F) * t * u7) +
        (32 : F) * t ^ 2 * ((8 : F) * s - (15 : F) * t ^ 2) =
        0 := by
    linear_combination (7 : F) * t * hT + (2 : F) * hU +
      (32 : F) * t ^ 2 * hM
  have h10 : (10 : F) ≠ 0 := by norm_num
  have ht4 : t ^ 4 = 0 := by
    have : (10 : F) * t ^ 4 = 0 := hid.symm.trans hleft
    exact (mul_eq_zero.mp this).resolve_left h10
  have ht0 : t = 0 := by
    have hprod : t * (t * (t * t)) = 0 := by
      have hcube : t * (t * (t * t)) = t ^ 4 := by ring
      rw [hcube, ht4]
    rcases mul_eq_zero.mp hprod with ht | hrest
    · exact ht
    · rcases mul_eq_zero.mp hrest with ht | hsq
      · exact ht
      · exact (mul_eq_zero.mp hsq).elim id id
  have h8 : (8 : F) ≠ 0 := by norm_num
  have hs0 : s = 0 := by
    have ht2 : t ^ 2 = 0 := by simp [ht0]
    have : (8 : F) * s = 0 := by
      linear_combination hM + (15 : F) * ht2
    exact (mul_eq_zero.mp this).resolve_left h8
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hu0 : u7 = 0 := by
    have ht3 : t ^ 3 = 0 := by simp [ht0]
    have : (64 : F) * u7 = 0 := by
      linear_combination hT + (128 : F) * s * ht0 - (220 : F) * ht3
    exact (mul_eq_zero.mp this).resolve_left h64
  exact ⟨ht0, hs0, hu0⟩

end FourthFaceScalars410

/-! ## Source-facing fourth-face packet -/

section NonzeroFourthFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The third quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹⁴`. -/
theorem nonzeroFace410_fourthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ delta : k,
      localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) lambda =
        Polynomial.C delta * h0 ^ 14 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = hRF ^ 4 := by
    simp only [hp4, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep :
      affineDepress68 hRF (quarticDepressionR410 hRF a3)
          (sourceToRatFunc68 p) =
        depressedQuartic46
          (depressedA46 hRF (quarticDepressionR410 hRF a3) a3 a2)
          (depressedB46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1)
          (depressedC46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 a0) := by
    change affineDepress46 hRF (quarticDepressionR410 hRF a3)
        (sourceToRatFunc46 p) = _
    exact affineDepress_sourceQuartic46 p hRF
      (quarticDepressionR410 hRF a3) hp hh hpTop
      (by simp [a3, quarticDepressionR410])
  have hNrat : 5 * a3 * hRF ^ 6 - 2 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH3 : algebraMap k[X] (RatFunc k) (H ^ 3) = hRF ^ 6 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9) =
        5 * a3 * hRF ^ 6 - 2 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a3, b9, hH3]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 =
        RatFunc.C (-lambda / 2) := by
    have hL := depressedL410_eq_of_ninthPower hRF a3 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (quarticDepressionR410 hRF a3) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3) (sourceToRatFunc68 q)
  have hf3 : f.coeff 3 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_three]
  have hf4 : f.coeff 4 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_four]
  have hf_high : ∀ n, 4 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_of_gt_four _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src
  have hg6 :
      g.coeff 6 =
        depressedR410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedR410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg8' :
      g.coeff 8 =
        depressedP410 hRF (quarticDepressionR410 hRF a3) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP410, depressedP810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 2) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * quarticDepressionR410 hRF a3 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 2) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf2 : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have hf1 : f.coeff 1 =
      depressedB410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 := by
    dsimp only [f, depressedB410, a3, a2, a1]
    rw [hpDep, coeff_depressedQuartic46_one]
  have hf0 : f.coeff 0 =
      depressedC410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 a0 := by
    dsimp only [f, depressedC410, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedQuartic46_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual410 (f.coeff 2) (g.coeff 8)) = 0 :=
    alphaResidual410_deriv_zero ratFuncDerivation68 (f.coeff 2)
      (g.coeff 8) hrow11
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow9)
  obtain ⟨delta0, hdelta0⟩ :
      ∃ a : k,
        gammaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 6) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hgamma0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        (128 : RatFunc k) * hRF ^ 14 *
          gammaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 6) := by
    have hF := fourthDefect_eq_clearedGamma410 hRF a3 a2 a1 a0 b9 b8 b7 b6
      (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedFourthDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b8,
      b7, b6, gammaResidual410, hf2, hf1, hf0, hg6, hg8', hg9L] using
      hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (128 * delta0) * h0 ^ 14) := by
    rw [hclear, hdelta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨128 * delta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

set_option maxHeartbeats 4000000 in
/-- Finite local initial packet: the third-face jet together with the
degree-`9` defect forces `h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`,
and `h⁸ ∣ q₉`. -/
theorem nonzeroFace410_linearRoot_fourthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
      h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
      h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨hp3div, hq8pow4, hq7div, _hq9pow7⟩ :=
    nonzeroFace410_linearRoot_thirdInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4 hq10 hN hD hroot
  obtain ⟨t, ht⟩ := hp3div
  obtain ⟨s, hs⟩ := hq8pow4
  obtain ⟨u7, hu7⟩ := hq7div
  have hM0 :
      (8 : k[X]) * s - (15 : k[X]) * t ^ 2 -
          (20 : k[X]) * p.coeff 2 * h0 ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 2 =
        Polynomial.C alpha * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
    calc
      h0 ^ 4 *
            ((8 : k[X]) * s - (15 : k[X]) * t ^ 2 -
                (20 : k[X]) * p.coeff 2 * h0 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t * h0 ^ 2) =
          localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect410, ht, hs]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM
      _ = h0 ^ 4 * (Polynomial.C alpha * h0 ^ 4) := by ring
  have hT0 :
      (64 : k[X]) * u7 - (128 : k[X]) * s * t + (220 : k[X]) * t ^ 3 +
          (80 : k[X]) * p.coeff 2 * t * h0 ^ 2 -
        (99 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 2 +
          (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 4 -
        (160 : k[X]) * p.coeff 1 * h0 ^ 5 =
        Polynomial.C gamma * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hh0)
    calc
      h0 ^ 5 *
            ((64 : k[X]) * u7 - (128 : k[X]) * s * t +
                (220 : k[X]) * t ^ 3 +
              (80 : k[X]) * p.coeff 2 * t * h0 ^ 2 -
                (99 : k[X]) * Polynomial.C lambda * t ^ 2 * h0 ^ 2 +
              (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 4 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 5) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, ht, hs, hu7]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hT
      _ = h0 ^ 5 * (Polynomial.C gamma * h0 ^ 6) := by ring
  have hU0 :
      (320 : k[X]) * s * t ^ 2 - (525 : k[X]) * t ^ 4 -
          (224 : k[X]) * t * u7 - (256 : k[X]) * p.coeff 2 * s * h0 ^ 2 +
        (400 : k[X]) * p.coeff 2 * t ^ 2 * h0 ^ 2 +
          (128 : k[X]) * q.coeff 6 * h0 ^ 2 +
        (210 : k[X]) * Polynomial.C lambda * t ^ 3 * h0 ^ 2 +
          (400 : k[X]) * p.coeff 2 ^ 2 * h0 ^ 4 -
        (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t * h0 ^ 4 +
          (80 : k[X]) * p.coeff 1 * t * h0 ^ 5 +
        (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 7 -
          (320 : k[X]) * p.coeff 0 * h0 ^ 8 =
        Polynomial.C delta * h0 ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 *
            ((320 : k[X]) * s * t ^ 2 - (525 : k[X]) * t ^ 4 -
                (224 : k[X]) * t * u7 -
              (256 : k[X]) * p.coeff 2 * s * h0 ^ 2 +
                (400 : k[X]) * p.coeff 2 * t ^ 2 * h0 ^ 2 +
              (128 : k[X]) * q.coeff 6 * h0 ^ 2 +
                (210 : k[X]) * Polynomial.C lambda * t ^ 3 * h0 ^ 2 +
              (400 : k[X]) * p.coeff 2 ^ 2 * h0 ^ 4 -
                (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t *
                    h0 ^ 4 +
              (80 : k[X]) * p.coeff 1 * t * h0 ^ 5 +
                (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 7 -
              (320 : k[X]) * p.coeff 0 * h0 ^ 8) =
          localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect410, ht, hs, hu7]
        ring
      _ = Polynomial.C delta * h0 ^ 14 := hU
      _ = h0 ^ 6 * (Polynomial.C delta * h0 ^ 8) := by ring
  have hMroot : (8 : k) * s.eval a - (15 : k) * (t.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (64 : k) * u7.eval a - (128 : k) * s.eval a * t.eval a +
      (220 : k) * (t.eval a) ^ 3 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (320 : k) * s.eval a * (t.eval a) ^ 2 -
      (525 : k) * (t.eval a) ^ 4 - (224 : k) * t.eval a * u7.eval a =
        0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  obtain ⟨ht0, hs0, hu0⟩ :=
    fourthFace_rootScalars_vanish410 (t.eval a) (s.eval a) (u7.eval a)
      hMroot hTroot hUroot
  have ht_div : h0 ∣ t :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 t a hh0degree hroot ht0
  have hs_div : h0 ∣ s :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 s a hh0degree hroot hs0
  have hu_div : h0 ∣ u7 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 u7 a hh0degree hroot hu0
  obtain ⟨t1, ht1⟩ := ht_div
  obtain ⟨s1, hs1⟩ := hs_div
  obtain ⟨v1, hv1⟩ := hu_div
  have hp3t1 : p.coeff 3 = h0 ^ 2 * t1 := by
    rw [ht, ht1]
    ring
  have hq8s1 : q.coeff 8 = h0 ^ 5 * s1 := by
    rw [hs, hs1]
    ring
  have hq7v1 : q.coeff 7 = h0 ^ 2 * v1 := by
    rw [hu7, hv1]
    ring
  have hM1 :
      (8 : k[X]) * s1 - (20 : k[X]) * p.coeff 2 * h0 -
          (15 : k[X]) * t1 ^ 2 * h0 +
        (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 2 =
        Polynomial.C alpha * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hh0)
    calc
      h0 ^ 5 *
            ((8 : k[X]) * s1 - (20 : k[X]) * p.coeff 2 * h0 -
                (15 : k[X]) * t1 ^ 2 * h0 +
              (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 2) =
          localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect410, hp3t1, hq8s1]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM
      _ = h0 ^ 5 * (Polynomial.C alpha * h0 ^ 3) := by ring
  have hT1 :
      (64 : k[X]) * v1 - (128 : k[X]) * s1 * t1 * h0 +
          (220 : k[X]) * t1 ^ 3 * h0 ^ 2 +
        (80 : k[X]) * p.coeff 2 * t1 * h0 ^ 2 -
          (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 3 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 3 -
          (160 : k[X]) * p.coeff 1 * h0 ^ 4 =
        Polynomial.C gamma * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 *
            ((64 : k[X]) * v1 - (128 : k[X]) * s1 * t1 * h0 +
                (220 : k[X]) * t1 ^ 3 * h0 ^ 2 +
              (80 : k[X]) * p.coeff 2 * t1 * h0 ^ 2 -
                (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 3 +
              (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 3 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 4) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, hp3t1, hq8s1, hq7v1]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hT
      _ = h0 ^ 6 * (Polynomial.C gamma * h0 ^ 5) := by ring
  have hU1 :
      (128 : k[X]) * q.coeff 6 - (224 : k[X]) * t1 * v1 +
          (320 : k[X]) * s1 * t1 ^ 2 * h0 -
        (525 : k[X]) * t1 ^ 4 * h0 ^ 2 -
          (256 : k[X]) * p.coeff 2 * s1 * h0 +
        (400 : k[X]) * p.coeff 2 * t1 ^ 2 * h0 ^ 2 +
          (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 3 +
        (400 : k[X]) * p.coeff 2 ^ 2 * h0 ^ 2 -
          (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 * h0 ^ 3 +
        (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 4 +
          (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 5 -
        (320 : k[X]) * p.coeff 0 * h0 ^ 6 =
        Polynomial.C delta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 hh0)
    calc
      h0 ^ 8 *
            ((128 : k[X]) * q.coeff 6 - (224 : k[X]) * t1 * v1 +
                (320 : k[X]) * s1 * t1 ^ 2 * h0 -
              (525 : k[X]) * t1 ^ 4 * h0 ^ 2 -
                (256 : k[X]) * p.coeff 2 * s1 * h0 +
              (400 : k[X]) * p.coeff 2 * t1 ^ 2 * h0 ^ 2 +
                (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 3 +
              (400 : k[X]) * p.coeff 2 ^ 2 * h0 ^ 2 -
                (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 *
                    h0 ^ 3 +
              (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 4 +
                (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 5 -
              (320 : k[X]) * p.coeff 0 * h0 ^ 6) =
          localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect410, hp3t1, hq8s1, hq7v1]
        ring
      _ = Polynomial.C delta * h0 ^ 14 := hU
      _ = h0 ^ 8 * (Polynomial.C delta * h0 ^ 6) := by ring
  have hs10 : s1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM1
    have h8 : (8 : k) ≠ 0 := by norm_num
    have h8s : (8 : k) * s1.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h8s).resolve_left h8
  have hv10 : v1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT1
    have h64 : (64 : k) ≠ 0 := by norm_num
    have h64v : (64 : k) * v1.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h64v).resolve_left h64
  have hq6root : (q.coeff 6).eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU1
    have h128 : (128 : k) ≠ 0 := by norm_num
    have h128q : (128 : k) * (q.coeff 6).eval a -
        (224 : k) * t1.eval a * v1.eval a = 0 := by
      simpa [hroot] using heval
    have : (128 : k) * (q.coeff 6).eval a = 0 := by
      linear_combination h128q + (224 : k) * t1.eval a * hv10
    exact (mul_eq_zero.mp this).resolve_left h128
  have hs1_div : h0 ∣ s1 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 s1 a hh0degree hroot hs10
  have hv1_div : h0 ∣ v1 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 v1 a hh0degree hroot hv10
  have hq6div : h0 ∣ q.coeff 6 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 6) a
      hh0degree hroot hq6root
  obtain ⟨s2, hs2⟩ := hs1_div
  obtain ⟨v2, hv2⟩ := hv1_div
  obtain ⟨w6, hw6⟩ := hq6div
  have hq8s2 : q.coeff 8 = h0 ^ 6 * s2 := by
    rw [hq8s1, hs2]
    ring
  have hq7v2 : q.coeff 7 = h0 ^ 3 * v2 := by
    rw [hq7v1, hv2]
    ring
  have hT2 :
      (64 : k[X]) * v2 - (128 : k[X]) * s2 * t1 * h0 +
          (220 : k[X]) * t1 ^ 3 * h0 +
        (80 : k[X]) * p.coeff 2 * t1 * h0 -
          (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 2 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 2 -
          (160 : k[X]) * p.coeff 1 * h0 ^ 3 =
        Polynomial.C gamma * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 7 hh0)
    calc
      h0 ^ 7 *
            ((64 : k[X]) * v2 - (128 : k[X]) * s2 * t1 * h0 +
                (220 : k[X]) * t1 ^ 3 * h0 +
              (80 : k[X]) * p.coeff 2 * t1 * h0 -
                (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 2 +
              (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 2 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 3) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, hp3t1, hq8s2, hq7v2]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hT
      _ = h0 ^ 7 * (Polynomial.C gamma * h0 ^ 4) := by ring
  have hv20 : v2.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT2
    have h64 : (64 : k) ≠ 0 := by norm_num
    have h64v : (64 : k) * v2.eval a = 0 := by
      simpa [hroot] using heval
    exact (mul_eq_zero.mp h64v).resolve_left h64
  have hv2_div : h0 ∣ v2 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 v2 a hh0degree hroot hv20
  obtain ⟨v3, hv3⟩ := hv2_div
  have hq7v3 : q.coeff 7 = h0 ^ 4 * v3 := by
    rw [hq7v2, hv3]
    ring
  have hU2 :
      (128 : k[X]) * w6 - (224 : k[X]) * t1 * v2 +
          (320 : k[X]) * s2 * t1 ^ 2 * h0 -
        (525 : k[X]) * t1 ^ 4 * h0 -
          (256 : k[X]) * p.coeff 2 * s2 * h0 +
        (400 : k[X]) * p.coeff 2 * t1 ^ 2 * h0 +
          (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 2 +
        (400 : k[X]) * p.coeff 2 ^ 2 * h0 -
          (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 * h0 ^ 2 +
        (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 3 +
          (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 4 -
        (320 : k[X]) * p.coeff 0 * h0 ^ 5 =
        Polynomial.C delta * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 hh0)
    calc
      h0 ^ 9 *
            ((128 : k[X]) * w6 - (224 : k[X]) * t1 * v2 +
                (320 : k[X]) * s2 * t1 ^ 2 * h0 -
              (525 : k[X]) * t1 ^ 4 * h0 -
                (256 : k[X]) * p.coeff 2 * s2 * h0 +
              (400 : k[X]) * p.coeff 2 * t1 ^ 2 * h0 +
                (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 2 +
              (400 : k[X]) * p.coeff 2 ^ 2 * h0 -
                (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 *
                    h0 ^ 2 +
              (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 3 +
                (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 4 -
              (320 : k[X]) * p.coeff 0 * h0 ^ 5) =
          localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect410, hp3t1, hq8s2, hq7v2, hw6]
        ring
      _ = Polynomial.C delta * h0 ^ 14 := hU
      _ = h0 ^ 9 * (Polynomial.C delta * h0 ^ 5) := by ring
  have hw60 : w6.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU2
    have h128 : (128 : k) ≠ 0 := by norm_num
    have h128w : (128 : k) * w6.eval a -
        (224 : k) * t1.eval a * v2.eval a = 0 := by
      simpa [hroot] using heval
    have : (128 : k) * w6.eval a = 0 := by
      linear_combination h128w + (224 : k) * t1.eval a * hv20
    exact (mul_eq_zero.mp this).resolve_left h128
  have hw6_div : h0 ∣ w6 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 w6 a hh0degree hroot hw60
  obtain ⟨w7, hw7⟩ := hw6_div
  have hp3pow : h0 ^ 2 ∣ p.coeff 3 := ⟨t1, by rw [hp3t1]⟩
  have hq8pow : h0 ^ 6 ∣ q.coeff 8 := ⟨s2, by rw [hq8s2]⟩
  have hq7pow : h0 ^ 4 ∣ q.coeff 7 := ⟨v3, by rw [hq7v3]⟩
  have hq6pow : h0 ^ 2 ∣ q.coeff 6 := ⟨w7, by rw [hw6, hw7]; ring⟩
  have hq9pow : h0 ^ 8 ∣ q.coeff 9 := by
    have h2 : (2 : k) ≠ 0 := by norm_num
    have hN' :
        (2 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 3 * h0 ^ 6 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      have hH3 : (h0 ^ 2) ^ 3 = h0 ^ 6 := by ring
      rw [hH3] at this
      linear_combination -this
    have hform :
        (2 : k[X]) * q.coeff 9 =
          h0 ^ 8 * ((5 : k[X]) * t1 - Polynomial.C lambda * h0) := by
      rw [hN', hp3t1]
      ring
    have hC2 : Polynomial.C (2 : k) = (2 : k[X]) :=
      Polynomial.C_eq_natCast 2
    have hq9eq : q.coeff 9 =
        C ((2 : k)⁻¹) * ((2 : k[X]) * q.coeff 9) := by
      have hone : (C ((2 : k)⁻¹) * C (2 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h2, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((2 : k)⁻¹) * C (2 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((2 : k)⁻¹) * (C (2 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((2 : k)⁻¹) * ((2 : k[X]) * q.coeff 9) := by rw [hC2]
    refine ⟨C ((2 : k)⁻¹) *
        ((5 : k[X]) * t1 - Polynomial.C lambda * h0), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp3pow, hq8pow, hq7pow, hq6pow, hq9pow⟩

/-- Source-facing fourth integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_fourthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda delta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda =
          Polynomial.C delta * h0 ^ 14 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, _a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨delta, hU⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, delta, hh0, hlambda, hh0degree, hH, hN', hU⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the degree-one scale divides `p₃` to order two, `q₈` to
order six, `q₇` to order four, `q₆` to order two, and `q₉` to order
eight. -/
theorem normalized410ScaleTwo_nonzeroFace_fourthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
        h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized410ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp3, hq8, hq7, hq6, hq9⟩ :=
    nonzeroFace410_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq6, hq9, hN'⟩

end NonzeroFourthFace410

#print axioms fourthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_9_monicQuarticDecic
#print axioms fourthDefect_eq_clearedGamma410
#print axioms nonzeroFace410_fourthDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_fourthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_fourthDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_fourthInitialPacket

end Max11DegreeRoutes
