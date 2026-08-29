import LowScale410ScaleTwoFourthFace

/-! # Scale-two fifth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the fourth face supplies the degree-`9` integral
`R - (5/2) C - (9/4) L B - 2 P A + (25/8) A²` and the local jet
`h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`, `h⁸ ∣ q₉`.  The next
Keller coefficient is the degree-`8` Jacobian row.  After the same
quartic depression that kills `z³`, that row is
`9 L C' + 8 P B' + 7 Q A' - B P' - 2 A Q' - 4 S' = 0`.  The resulting
first integral clears to a polynomial defect `V` of weight seventeen.

Evaluating the second, third, fourth, and fifth defects together at
the root of `h` does not force a further individual vanishing.  It
does force the mixed relation
`3 t₁⁵ - 40 p₂ t₁³ + 240 p₂² t₁ - 256 q₅ = 0` on the jets
`p₃ = t₁ h²` and `q₅`, equivalently
`h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The fifth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z⁰`/`z⁵` defect after the degree-`9` integral. -/
theorem fifthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        p.coeff 1 * (q.coeff 8).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC5, hC6, hC7, hC8, hC9, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z⁵` coordinates -/

section Depression410Fifth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁵` coefficient. -/
def depressedS410 (h r b9 b8 b7 b6 b5 : F) : F :=
  -252 * r ^ 5 + 126 * (b9 / h ^ 9) * r ^ 4 -
    56 * (b8 / h ^ 8) * r ^ 3 + 21 * (b7 / h ^ 7) * r ^ 2 -
    6 * (b6 / h ^ 6) * r + b5 / h ^ 5

/-- First residual of the degree-`8` row.  Equivalent to
`S - (9/4) L C - 2 α B - (7/4) β A - (15/4) A B - (45/32) L A²`
on the second- and third-face integrals. -/
def deltaResidual410 (L A B C0 P Q S0 : F) : F :=
  S0 - (9 / 4 : F) * L * C0 -
    (2 : F) * alphaResidual410 A P * B -
    (7 / 4 : F) * betaResidual410 L A B Q * A -
    (15 / 4 : F) * A * B - (45 / 32 : F) * L * A ^ 2

/-- Polynomial numerator of `4096 h¹⁷ δ` on the ninth-power face. -/
def localClearedFifthDefect410
    (h a3 a2 a1 a0 b8 b7 b6 b5 : F[X]) (lambda : F) : F[X] :=
  (4096 : F[X]) * b5 * h ^ 12 -
    (6144 : F[X]) * a3 * b6 * h ^ 8 +
    (8064 : F[X]) * a3 ^ 2 * b7 * h ^ 4 -
    (9984 : F[X]) * a3 ^ 3 * b8 +
    (15912 : F[X]) * a3 ^ 5 * h ^ 2 -
    (5967 : F[X]) * Polynomial.C lambda * a3 ^ 4 * h ^ 5 -
    (31200 : F[X]) * a2 * a3 ^ 3 * h ^ 6 +
    (18432 : F[X]) * a2 * a3 * b8 * h ^ 4 -
    (7168 : F[X]) * a2 * b7 * h ^ 8 +
    (16848 : F[X]) * Polynomial.C lambda * a2 * a3 ^ 2 * h ^ 9 -
    (11520 : F[X]) * a2 ^ 2 * a3 * h ^ 10 +
    (14400 : F[X]) * a1 * a3 ^ 2 * h ^ 10 -
    (8192 : F[X]) * a1 * b8 * h ^ 8 -
    (5184 : F[X]) * Polynomial.C lambda * a2 ^ 2 * h ^ 13 -
    (10368 : F[X]) * Polynomial.C lambda * a1 * a3 * h ^ 13 +
    (23040 : F[X]) * a1 * a2 * h ^ 14 +
    (4608 : F[X]) * Polynomial.C lambda * a0 * h ^ 17

/-- Mixed fifth-face combination
`3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰`. -/
def localFifthMixed410 (h a3 a2 b5 : F[X]) : F[X] :=
  (3 : F[X]) * a3 ^ 5 -
    (40 : F[X]) * a2 * a3 ^ 3 * h ^ 4 +
    (240 : F[X]) * a2 ^ 2 * a3 * h ^ 8 -
    (256 : F[X]) * b5 * h ^ 10

/-- Exact denominator clearing for the decic `z⁵` coordinate on the
ninth-power face. -/
theorem depressedS410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 =
      (252 * a3 ^ 5 * h ^ 2 - 63 * lambda * a3 ^ 4 * h ^ 5 -
          224 * a3 ^ 3 * b8 + 336 * a3 ^ 2 * b7 * h ^ 4 -
          384 * a3 * b6 * h ^ 8 + 256 * b5 * h ^ 12) /
        (256 * h ^ 17) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh17 : h ^ 17 ≠ 0 := pow_ne_zero 17 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedS410, quarticDepressionR410, quarticDepressionR46]
  have hrewrite :
      -252 * (a3 / (4 * h ^ 3)) ^ 5 +
          126 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 4 -
        56 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) ^ 3 +
          21 * (b7 / h ^ 7) * (a3 / (4 * h ^ 3)) ^ 2 -
        6 * (b6 / h ^ 6) * (a3 / (4 * h ^ 3)) + b5 / h ^ 5 =
        (252 * a3 ^ 5 * h ^ 2 - 63 * lambda * a3 ^ 4 * h ^ 5 -
            224 * a3 ^ 3 * b8 + 336 * a3 ^ 2 * b7 * h ^ 4 -
            384 * a3 * b6 * h ^ 8 + 256 * b5 * h ^ 12) /
          (256 * h ^ 17) := by
    field_simp [hh, h2, h4, hh3, hh5, hh6, hh7, hh8pow, hh9, hh17, h256]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh5, hh6, hh7, hh8pow, hh9, hh17, h256]
    ring
  exact hrewrite

set_option maxHeartbeats 4000000 in
/-- Clearing the first integral
`S - (9/4) L C - 2 α B - (7/4) β A - (15/4) A B - (45/32) L A²`
against `h¹⁷` on the ninth-power face. -/
theorem fifthDefect_eq_clearedDelta410
    (h a3 a2 a1 a0 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (4096 : F) * h ^ 17 *
        deltaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
          (depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5) =
      (4096 : F) * b5 * h ^ 12 - (6144 : F) * a3 * b6 * h ^ 8 +
        (8064 : F) * a3 ^ 2 * b7 * h ^ 4 - (9984 : F) * a3 ^ 3 * b8 +
        (15912 : F) * a3 ^ 5 * h ^ 2 -
        (5967 : F) * lambda * a3 ^ 4 * h ^ 5 -
        (31200 : F) * a2 * a3 ^ 3 * h ^ 6 +
        (18432 : F) * a2 * a3 * b8 * h ^ 4 -
        (7168 : F) * a2 * b7 * h ^ 8 +
        (16848 : F) * lambda * a2 * a3 ^ 2 * h ^ 9 -
        (11520 : F) * a2 ^ 2 * a3 * h ^ 10 +
        (14400 : F) * a1 * a3 ^ 2 * h ^ 10 -
        (8192 : F) * a1 * b8 * h ^ 8 -
        (5184 : F) * lambda * a2 ^ 2 * h ^ 13 -
        (10368 : F) * lambda * a1 * a3 * h ^ 13 +
        (23040 : F) * a1 * a2 * h ^ 14 +
        (4608 : F) * lambda * a0 * h ^ 17 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hh12 : h ^ 12 ≠ 0 := pow_ne_zero 12 hh
  have hh17 : h ^ 17 ≠ 0 := pow_ne_zero 17 hh
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
  have hQ :
      depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 =
        (30 * a3 ^ 3 * h ^ 2 - 9 * lambda * a3 ^ 2 * h ^ 5 -
            16 * a3 * b8 + 8 * b7 * h ^ 4) / (8 * h ^ 11) :=
    depressedQ410_eq_cleared h a3 b9 b8 b7 lambda hh hN
  have hS :
      depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 =
        (252 * a3 ^ 5 * h ^ 2 - 63 * lambda * a3 ^ 4 * h ^ 5 -
            224 * a3 ^ 3 * b8 + 336 * a3 ^ 2 * b7 * h ^ 4 -
            384 * a3 * b6 * h ^ 8 + 256 * b5 * h ^ 12) /
          (256 * h ^ 17) :=
    depressedS410_eq_cleared h a3 b9 b8 b7 b6 b5 lambda hh hN
  have h256S :
      (256 : F) * h ^ 17 *
          depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 =
        (252 : F) * a3 ^ 5 * h ^ 2 - (63 : F) * lambda * a3 ^ 4 * h ^ 5 -
          (224 : F) * a3 ^ 3 * b8 + (336 : F) * a3 ^ 2 * b7 * h ^ 4 -
          (384 : F) * a3 * b6 * h ^ 8 + (256 : F) * b5 * h ^ 12 := by
    rw [hS]
    field_simp [hh, h256, hh17]
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
  have h256C :
      (256 : F) * h ^ 12 *
          depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
        (256 : F) * a0 * h ^ 12 - (64 : F) * a1 * a3 * h ^ 8 +
          (16 : F) * a2 * a3 ^ 2 * h ^ 4 - (3 : F) * a3 ^ 4 := by
    rw [hC]
    field_simp [hh, h256, hh12]
    try ring
  have h8alpha :
      (8 : F) * h ^ 8 *
          alphaResidual410
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8) =
        (8 : F) * b8 - (20 : F) * a2 * h ^ 6 +
          (9 : F) * lambda * a3 * h ^ 5 - (15 : F) * a3 ^ 2 * h ^ 2 :=
    secondDefect_eq_clearedAlpha410 h a3 a2 b9 b8 lambda hh hN
  have h64beta :
      (64 : F) * h ^ 11 *
          betaResidual410
            (depressedL410 h (quarticDepressionR410 h a3) b9)
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
            (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7) =
        (220 : F) * a3 ^ 3 * h ^ 2 - (99 : F) * lambda * a3 ^ 2 * h ^ 5 -
          (128 : F) * a3 * b8 + (64 : F) * b7 * h ^ 4 +
          (80 : F) * a2 * a3 * h ^ 6 - (160 : F) * a1 * h ^ 10 +
          (72 : F) * lambda * a2 * h ^ 9 :=
    thirdDefect_eq_clearedBeta410 h a3 a2 a1 b9 b8 b7 lambda hh hN
  have h16S :
      (4096 : F) * h ^ 17 *
          depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 =
        (16 : F) *
          ((256 : F) * h ^ 17 *
            depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
              b5) := by
    ring
  have h18C :
      (4608 : F) * lambda * h ^ 17 *
          depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 =
        (18 : F) * lambda * h ^ 5 *
          ((256 : F) * h ^ 12 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
              a0) := by
    ring
  have h128alphaB :
      (8192 : F) * h ^ 17 *
          (alphaResidual410
              (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
              (depressedP410 h (quarticDepressionR410 h a3) b9 b8) *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) =
        (128 : F) *
          ((8 : F) * h ^ 8 *
              alphaResidual410
                (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
                (depressedP410 h (quarticDepressionR410 h a3) b9
                  b8)) *
            ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) := by
    ring
  have h14betaA :
      (7168 : F) * h ^ 17 *
          (betaResidual410
              (depressedL410 h (quarticDepressionR410 h a3) b9)
              (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
              (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
              (depressedQ410 h (quarticDepressionR410 h a3) b9 b8
                b7) *
            depressedA410 h (quarticDepressionR410 h a3) a3 a2) =
        (14 : F) *
          ((64 : F) * h ^ 11 *
              betaResidual410
                (depressedL410 h (quarticDepressionR410 h a3) b9)
                (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
                (depressedB410 h (quarticDepressionR410 h a3) a3 a2
                  a1)
                (depressedQ410 h (quarticDepressionR410 h a3) b9 b8
                  b7)) *
            ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3
                a2) := by
    ring
  have h240AB :
      (15360 : F) * h ^ 17 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) =
        (240 : F) * h ^ 2 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) *
            ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) := by
    ring
  have h45A2 :
      (2880 : F) * lambda * h ^ 17 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^ 2 =
        (45 : F) * lambda * h ^ 5 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3
                a2) ^ 2 := by
    field_simp [hh, h8, hh6, hh17]
    ring
  have hdiff :
      (4096 : F) * h ^ 17 *
          deltaResidual410
            (depressedL410 h (quarticDepressionR410 h a3) b9)
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
            (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
            (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
            (depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
              b5) =
        (4096 : F) * h ^ 17 *
            depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
              b5 +
          (4608 : F) * lambda * h ^ 17 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0 -
          (8192 : F) * h ^ 17 *
            (alphaResidual410
                (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
                (depressedP410 h (quarticDepressionR410 h a3) b9
                  b8) *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) -
          (7168 : F) * h ^ 17 *
            (betaResidual410
                (depressedL410 h (quarticDepressionR410 h a3) b9)
                (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
                (depressedB410 h (quarticDepressionR410 h a3) a3 a2
                  a1)
                (depressedQ410 h (quarticDepressionR410 h a3) b9 b8
                  b7) *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) -
          (15360 : F) * h ^ 17 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) +
          (2880 : F) * lambda * h ^ 17 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^
              2 := by
    simp only [deltaResidual410, hL]
    field_simp [h2, h4, h8, h32]
    ring
  rw [hdiff, h16S, h256S, h18C, h256C, h128alphaB, h8alpha, h8B,
    h14betaA, h64beta, h8A, h240AB, h8A, h8B, h45A2, h8A]
  ring

end Depression410Fifth

/-! ## Degree-`8` depressed Jacobian coefficient -/

section DepressedRow410Fifth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`8` Jacobian coefficient is
exactly `9 L C' + 8 P B' + 7 Q A' - B P' - 2 A Q' - 4 S'`. -/
theorem differentialJacobian_coeff_8_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 8 =
      (9 : F) * g.coeff 9 * d (f.coeff 0) +
        (8 : F) * g.coeff 8 * d (f.coeff 1) +
        (7 : F) * g.coeff 7 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 8) -
          (2 : F) * f.coeff 2 * d (g.coeff 7) -
          (4 : F) * d (g.coeff 5) := by
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
  have hmem08 : ((0, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 8 =
        (9 : F) * g.coeff 9 * d (f.coeff 0) +
          (8 : F) * g.coeff 8 * d (f.coeff 1) +
          (7 : F) * g.coeff 7 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 8) : ℕ × ℕ) ≠ (1, 7) := by decide
    have hne02 : ((0, 8) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hne12 : ((1, 7) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hsubset : ({(0, 8), (1, 7), (2, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (8 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem08
      · subst b
        exact hmem17
      · subst b
        exact hmem26
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 8), (1, 7), (2, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 8 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 8) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 7) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne26 : b ≠ (2, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne08
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne17
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne26
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 8), (1, 7), (2, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 6 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
      ring
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
      coeff_coefficientDeriv, hder8, hder7, hder6]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 8 =
        f.coeff 1 * d (g.coeff 8) +
          (2 : F) * f.coeff 2 * d (g.coeff 7) +
          (4 : F) * d (g.coeff 5) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 8) : ℕ × ℕ) ≠ (1, 7) := by decide
    have hne08_35 : ((0, 8) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne17_35 : ((1, 7) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hsubset : ({(0, 8), (1, 7), (3, 5)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (8 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem08
      · subst b
        exact hmem17
      · subst b
        exact hmem35
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 8), (1, 7), (3, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 8 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 8) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 7) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne35 : b ≠ (3, 5) := by
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
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne08
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne17
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne35
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 8), (1, 7), (3, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 5 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_35]),
        Finset.sum_insert (by simp [hne17_35]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem deltaResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q S0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hrow : (9 : F) * L * d C0 + (8 : F) * P * d B +
        (7 : F) * Q * d A - B * d P - (2 : F) * A * d Q -
        (4 : F) * d S0 = 0) :
    d (deltaResidual410 L A B C0 P Q S0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h7]
  have h458 : d (45 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h45]
  have h8132 : d (81 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h81]
  have hP0 : d P - (5 / 2 : F) * d A = 0 := by
    have halpha' : d P - (5 / 2 : F) * d A = 0 := by
      simpa [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
        add_zero] using halpha
    exact halpha'
  have hQ0 : d Q - (5 / 2 : F) * d B - (9 / 4 : F) * L * d A = 0 := by
    have hbeta' :
        d Q - (5 / 2 : F) * d B - (9 / 4 : F) * L * d A = 0 := by
      simpa [betaResidual410, map_sub, Derivation.leibniz, h52, h94, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    exact hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hexp :
      deltaResidual410 L A B C0 P Q S0 =
        S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
          (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
          (81 / 32 : F) * L * (A * A) := by
    simp only [deltaResidual410, alphaResidual410, betaResidual410, pow_two]
    ring
  have hPderiv : d P = (5 / 2 : F) * d A := by
    linear_combination hP0
  have hQderiv : d Q = (5 / 2 : F) * d B + (9 / 4 : F) * L * d A := by
    linear_combination hQ0
  have hSderiv :
      d S0 = (9 / 4 : F) * L * d C0 + (2 : F) * P * d B +
        (7 / 4 : F) * Q * d A - (1 / 4 : F) * B * d P -
        (1 / 2 : F) * A * d Q := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d S0 - (9 / 4 : F) * L * d C0 - (2 : F) * B * d P -
          (2 : F) * P * d B - (7 / 4 : F) * A * d Q -
          (7 / 4 : F) * Q * d A + (45 / 8 : F) * B * d A +
          (45 / 8 : F) * A * d B + (81 / 16 : F) * L * A * d A = 0 := by
    rw [hSderiv, hPderiv, hQderiv]
    ring
  rw [hexp]
  simp [map_sub, map_add, Derivation.leibniz, h2, h4, h8, h32, h52, h94,
    h74, h458, h8132, hL, hsq, zero_mul, add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Fifth

/-! ## Affine depression of a degree-ten source, `z⁵` coefficient -/

section AffineDecic410Fifth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁵` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff5_410
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

end AffineDecic410Fifth

/-! ## Local scalar identity at a simple root -/

section FifthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The fourth-face jet reduces `M`, `T`, `U`, and `V` to a finite scalar
system in `(t₁, p₂, s₂, v₃, w₇, q₅)`.  That system forces the mixed
relation `3 t₁⁵ - 40 p₂ t₁³ + 240 p₂² t₁ - 256 q₅ = 0` and does not
force any individual vanishing. -/
theorem fifthFace_rootMixed_410
    (t1 a2 s2 v3 w7 b5 : F)
    (hM : (8 : F) * s2 - (20 : F) * a2 - (15 : F) * t1 ^ 2 = 0)
    (hT : (64 : F) * v3 - (128 : F) * s2 * t1 + (220 : F) * t1 ^ 3 +
        (80 : F) * a2 * t1 = 0)
    (hU : (128 : F) * w7 - (224 : F) * t1 * v3 +
        (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
        (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
        (400 : F) * a2 ^ 2 = 0)
    (hV : (4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
        (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
        (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
        (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
        (6144 : F) * t1 * w7 = 0) :
    (3 : F) * t1 ^ 5 - (40 : F) * a2 * t1 ^ 3 +
      (240 : F) * a2 ^ 2 * t1 - (256 : F) * b5 = 0 := by
  have hid :
      (4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
            (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
            (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
            (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
            (6144 : F) * t1 * w7 +
          (1024 : F) * a2 * t1 *
            ((8 : F) * s2 - (20 : F) * a2 - (15 : F) * t1 ^ 2) +
        ((112 : F) * a2 + (42 : F) * t1 ^ 2) *
            ((64 : F) * v3 - (128 : F) * s2 * t1 +
              (220 : F) * t1 ^ 3 + (80 : F) * a2 * t1) +
          (48 : F) * t1 *
            ((128 : F) * w7 - (224 : F) * t1 * v3 +
              (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
              (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
              (400 : F) * a2 ^ 2) =
        -(16 : F) *
          ((3 : F) * t1 ^ 5 - (40 : F) * a2 * t1 ^ 3 +
            (240 : F) * a2 ^ 2 * t1 - (256 : F) * b5) := by
    ring
  have hleft :
      (4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
            (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
            (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
            (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
            (6144 : F) * t1 * w7 +
          (1024 : F) * a2 * t1 *
            ((8 : F) * s2 - (20 : F) * a2 - (15 : F) * t1 ^ 2) +
        ((112 : F) * a2 + (42 : F) * t1 ^ 2) *
            ((64 : F) * v3 - (128 : F) * s2 * t1 +
              (220 : F) * t1 ^ 3 + (80 : F) * a2 * t1) +
          (48 : F) * t1 *
            ((128 : F) * w7 - (224 : F) * t1 * v3 +
              (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
              (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
              (400 : F) * a2 ^ 2) =
        0 := by
    linear_combination hV + (1024 : F) * a2 * t1 * hM +
      ((112 : F) * a2 + (42 : F) * t1 ^ 2) * hT + (48 : F) * t1 * hU
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hneg :
      -(16 : F) *
          ((3 : F) * t1 ^ 5 - (40 : F) * a2 * t1 ^ 3 +
            (240 : F) * a2 ^ 2 * t1 - (256 : F) * b5) = 0 :=
    hid.symm.trans hleft
  exact (mul_eq_zero.mp (by linear_combination -hneg)).resolve_left h16

end FifthFaceScalars410

/-! ## Source-facing fifth-face packet -/

section NonzeroFifthFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The fourth quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h¹⁷`. -/
theorem nonzeroFace410_fifthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eps : k,
      localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          lambda =
        Polynomial.C eps * h0 ^ 17 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
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
  have hg7 :
      g.coeff 7 =
        depressedQ410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedQ410, depressedQ810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg5 :
      g.coeff 5 =
        depressedS410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedS410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
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
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
          (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
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
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (g.coeff 7)) = 0 :=
    betaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (g.coeff 7) hLconst (by simpa using hrow10)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 5)) = 0 :=
    deltaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 5) hLconst halpha0 hbeta0 (by simpa using hrow8)
  obtain ⟨eps0, heps0⟩ :
      ∃ a : k,
        deltaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 5) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hdelta0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda) =
        (4096 : RatFunc k) * hRF ^ 17 *
          deltaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 5) := by
    have hF := fifthDefect_eq_clearedDelta410 hRF a3 a2 a1 a0 b9 b8 b7 b6
      b5 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedFifthDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b8,
      b7, b6, b5, deltaResidual410, alphaResidual410, betaResidual410, hf2,
      hf1, hf0, hg5, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (4096 * eps0) * h0 ^ 17) := by
    rw [hclear, heps0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨4096 * eps0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

set_option maxHeartbeats 4000000 in
/-- Finite local initial packet: the fourth-face jet together with the
degree-`8` defect forces the mixed divisibility
`h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰`
at the degree-one root. -/
theorem nonzeroFace410_linearRoot_fifthInitialPacket
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
      h0 ^ 8 ∣ q.coeff 9 ∧
      h0 ^ 11 ∣ localFifthMixed410 h0 (p.coeff 3) (p.coeff 2)
        (q.coeff 5) := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace410_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨eps, hV⟩ :=
    nonzeroFace410_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨hp3pow, hq8pow, hq7pow, hq6pow, hq9pow⟩ :=
    nonzeroFace410_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4 hq10 hN hD hroot
  obtain ⟨t1, ht1⟩ := hp3pow
  obtain ⟨s2, hs2⟩ := hq8pow
  obtain ⟨v3, hv3⟩ := hq7pow
  obtain ⟨w7, hw7⟩ := hq6pow
  have hM0 :
      (8 : k[X]) * s2 - (20 : k[X]) * p.coeff 2 -
          (15 : k[X]) * t1 ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * t1 * h0 =
        Polynomial.C alpha * h0 ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
    calc
      h0 ^ 6 *
            ((8 : k[X]) * s2 - (20 : k[X]) * p.coeff 2 -
                (15 : k[X]) * t1 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t1 * h0) =
          localClearedSecondDefect410 h0 (p.coeff 3) (p.coeff 2)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect410, ht1, hs2]
        ring
      _ = Polynomial.C alpha * h0 ^ 8 := hM
      _ = h0 ^ 6 * (Polynomial.C alpha * h0 ^ 2) := by ring
  have hT0 :
      (64 : k[X]) * v3 - (128 : k[X]) * s2 * t1 +
          (220 : k[X]) * t1 ^ 3 + (80 : k[X]) * p.coeff 2 * t1 +
        (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
          (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
        (160 : k[X]) * p.coeff 1 * h0 ^ 2 =
        Polynomial.C gamma * h0 ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 8 hh0)
    calc
      h0 ^ 8 *
            ((64 : k[X]) * v3 - (128 : k[X]) * s2 * t1 +
                (220 : k[X]) * t1 ^ 3 +
              (80 : k[X]) * p.coeff 2 * t1 +
                (72 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 -
              (99 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 -
                (160 : k[X]) * p.coeff 1 * h0 ^ 2) =
          localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect410, ht1, hs2, hv3]
        ring
      _ = Polynomial.C gamma * h0 ^ 11 := hT
      _ = h0 ^ 8 * (Polynomial.C gamma * h0 ^ 3) := by ring
  have hU0 :
      (128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
          (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
        (256 : k[X]) * p.coeff 2 * s2 +
          (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
        (400 : k[X]) * p.coeff 2 ^ 2 +
          (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 -
        (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 * h0 +
          (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 2 +
        (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 3 -
          (320 : k[X]) * p.coeff 0 * h0 ^ 4 =
        Polynomial.C delta * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
    calc
      h0 ^ 10 *
            ((128 : k[X]) * w7 - (224 : k[X]) * t1 * v3 +
                (320 : k[X]) * s2 * t1 ^ 2 - (525 : k[X]) * t1 ^ 4 -
              (256 : k[X]) * p.coeff 2 * s2 +
                (400 : k[X]) * p.coeff 2 * t1 ^ 2 +
              (400 : k[X]) * p.coeff 2 ^ 2 +
                (210 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 -
              (360 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 *
                  h0 +
                (80 : k[X]) * p.coeff 1 * t1 * h0 ^ 2 +
              (144 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 3 -
                (320 : k[X]) * p.coeff 0 * h0 ^ 4) =
          localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect410, ht1, hs2, hv3, hw7]
        ring
      _ = Polynomial.C delta * h0 ^ 14 := hU
      _ = h0 ^ 10 * (Polynomial.C delta * h0 ^ 4) := by ring
  have hV0 :
      (4096 : k[X]) * q.coeff 5 - (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
          (18432 : k[X]) * p.coeff 2 * s2 * t1 -
        (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
          (7168 : k[X]) * p.coeff 2 * v3 -
        (9984 : k[X]) * s2 * t1 ^ 3 + (15912 : k[X]) * t1 ^ 5 +
          (8064 : k[X]) * t1 ^ 2 * v3 - (6144 : k[X]) * t1 * w7 +
        (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 2 *
            h0 -
          (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * h0 -
        (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 * h0 +
          (23040 : k[X]) * p.coeff 1 * p.coeff 2 * h0 ^ 2 +
        (14400 : k[X]) * p.coeff 1 * t1 ^ 2 * h0 ^ 2 -
          (8192 : k[X]) * p.coeff 1 * s2 * h0 ^ 2 -
        (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 * h0 ^ 3 +
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * h0 ^ 5 =
        Polynomial.C eps * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hh0)
    calc
      h0 ^ 12 *
            ((4096 : k[X]) * q.coeff 5 -
                (11520 : k[X]) * p.coeff 2 ^ 2 * t1 +
              (18432 : k[X]) * p.coeff 2 * s2 * t1 -
                (31200 : k[X]) * p.coeff 2 * t1 ^ 3 -
              (7168 : k[X]) * p.coeff 2 * v3 -
                (9984 : k[X]) * s2 * t1 ^ 3 +
              (15912 : k[X]) * t1 ^ 5 +
                (8064 : k[X]) * t1 ^ 2 * v3 -
              (6144 : k[X]) * t1 * w7 +
                (16848 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    t1 ^ 2 * h0 -
              (5184 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 *
                  h0 -
                (5967 : k[X]) * Polynomial.C lambda * t1 ^ 4 * h0 +
              (23040 : k[X]) * p.coeff 1 * p.coeff 2 * h0 ^ 2 +
                (14400 : k[X]) * p.coeff 1 * t1 ^ 2 * h0 ^ 2 -
              (8192 : k[X]) * p.coeff 1 * s2 * h0 ^ 2 -
                (10368 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 *
                    h0 ^ 3 +
              (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 *
                  h0 ^ 5) =
          localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda := by
        simp only [localClearedFifthDefect410, ht1, hs2, hv3, hw7]
        ring
      _ = Polynomial.C eps * h0 ^ 17 := hV
      _ = h0 ^ 12 * (Polynomial.C eps * h0 ^ 5) := by ring
  have hMroot : (8 : k) * s2.eval a - (20 : k) * (p.coeff 2).eval a -
      (15 : k) * (t1.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (64 : k) * v3.eval a - (128 : k) * s2.eval a * t1.eval a +
      (220 : k) * (t1.eval a) ^ 3 +
        (80 : k) * (p.coeff 2).eval a * t1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (128 : k) * w7.eval a - (224 : k) * t1.eval a * v3.eval a +
      (320 : k) * s2.eval a * (t1.eval a) ^ 2 -
        (525 : k) * (t1.eval a) ^ 4 -
      (256 : k) * (p.coeff 2).eval a * s2.eval a +
        (400 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 2 +
      (400 : k) * ((p.coeff 2).eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  have hVroot : (4096 : k) * (q.coeff 5).eval a -
      (11520 : k) * ((p.coeff 2).eval a) ^ 2 * t1.eval a +
        (18432 : k) * (p.coeff 2).eval a * s2.eval a * t1.eval a -
      (31200 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 3 -
        (7168 : k) * (p.coeff 2).eval a * v3.eval a -
      (9984 : k) * s2.eval a * (t1.eval a) ^ 3 +
        (15912 : k) * (t1.eval a) ^ 5 +
      (8064 : k) * (t1.eval a) ^ 2 * v3.eval a -
        (6144 : k) * t1.eval a * w7.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hV0
    simpa [hroot] using heval
  have hmix :
      (3 : k) * (t1.eval a) ^ 5 -
          (40 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 3 +
        (240 : k) * ((p.coeff 2).eval a) ^ 2 * t1.eval a -
          (256 : k) * (q.coeff 5).eval a = 0 :=
    fifthFace_rootMixed_410 (t1.eval a) ((p.coeff 2).eval a)
      (s2.eval a) (v3.eval a) (w7.eval a) ((q.coeff 5).eval a)
      hMroot hTroot hUroot hVroot
  have hform :
      localFifthMixed410 h0 (p.coeff 3) (p.coeff 2) (q.coeff 5) =
        h0 ^ 10 *
          ((3 : k[X]) * t1 ^ 5 - (40 : k[X]) * p.coeff 2 * t1 ^ 3 +
            (240 : k[X]) * p.coeff 2 ^ 2 * t1 -
              (256 : k[X]) * q.coeff 5) := by
    simp only [localFifthMixed410, ht1]
    ring
  have hjet0 :
      ((3 : k[X]) * t1 ^ 5 - (40 : k[X]) * p.coeff 2 * t1 ^ 3 +
          (240 : k[X]) * p.coeff 2 ^ 2 * t1 -
            (256 : k[X]) * q.coeff 5).eval a = 0 := by
    have heval :
        ((3 : k[X]) * t1 ^ 5 - (40 : k[X]) * p.coeff 2 * t1 ^ 3 +
              (240 : k[X]) * p.coeff 2 ^ 2 * t1 -
            (256 : k[X]) * q.coeff 5).eval a =
          (3 : k) * (t1.eval a) ^ 5 -
            (40 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 3 +
          (240 : k) * ((p.coeff 2).eval a) ^ 2 * t1.eval a -
            (256 : k) * (q.coeff 5).eval a := by
      simp [eval_pow]
    rw [heval]
    linear_combination hmix
  have hjetdiv : h0 ∣
      (3 : k[X]) * t1 ^ 5 - (40 : k[X]) * p.coeff 2 * t1 ^ 3 +
        (240 : k[X]) * p.coeff 2 ^ 2 * t1 - (256 : k[X]) * q.coeff 5 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      ((3 : k[X]) * t1 ^ 5 - (40 : k[X]) * p.coeff 2 * t1 ^ 3 +
        (240 : k[X]) * p.coeff 2 ^ 2 * t1 - (256 : k[X]) * q.coeff 5)
      a hh0degree hroot hjet0
  obtain ⟨rQ, hrQ⟩ := hjetdiv
  refine ⟨⟨t1, ht1⟩, ⟨s2, hs2⟩, ⟨v3, hv3⟩, ⟨w7, hw7⟩, hq9pow, ⟨rQ, ?_⟩⟩
  rw [hform, hrQ]
  ring

/-- Source-facing fifth integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_fifthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eps : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) lambda =
          Polynomial.C eps * h0 ^ 17 := by
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
  obtain ⟨eps, hV⟩ :=
    nonzeroFace410_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, eps, hh0, hlambda, hh0degree, hH, hN', hV⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the fourth-face jet together with the mixed relation
`h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰`. -/
theorem normalized410ScaleTwo_nonzeroFace_fifthInitialPacket
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
        h0 ^ 11 ∣ localFifthMixed410 h0 (p.coeff 3) (p.coeff 2)
          (q.coeff 5) ∧
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
  obtain ⟨hp3, hq8, hq7, hq6, hq9, hmix⟩ :=
    nonzeroFace410_linearRoot_fifthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq6, hq9, hmix, hN'⟩

end NonzeroFifthFace410

#print axioms fifthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_8_monicQuarticDecic
#print axioms fifthDefect_eq_clearedDelta410
#print axioms nonzeroFace410_fifthDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_fifthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_fifthDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_fifthInitialPacket

end Max11DegreeRoutes
