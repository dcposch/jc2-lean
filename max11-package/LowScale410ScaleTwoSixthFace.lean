import LowScale410ScaleTwoFifthFace

/-! # Scale-two sixth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the fifth face supplies the degree-`8` integral and
the local jet `h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`, `h⁸ ∣ q₉`
together with `h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰`.
The next Keller coefficient is the degree-`7` Jacobian row.  After the
same quartic depression that kills `z³`, that row is
`8 P C' + 7 Q B' + 6 R A' - B Q' - 2 A R' - 4 T' = 0`.  The resulting
first integral clears to a polynomial defect `W` of weight twenty.

Evaluating the second through sixth defects together at the root of `h`
forces the mixed relation `t₁² - 4 p₂ = 0` on the jets `p₃ = t₁ h²`
and `p₂`, equivalently `h⁵ ∣ p₃² - 4 p₂ h⁴`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z⁰`/`z⁴` defect after the degree-`8` integral. -/
theorem sixthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) =
      0 := by
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
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC4, hC5, hC6, hC7, hC8, hC3, hC2]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z⁴` coordinates -/

section Depression410Sixth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁴` coefficient. -/
def depressedT410 (h r b9 b8 b7 b6 b5 b4 : F) : F :=
  210 * r ^ 6 - 126 * (b9 / h ^ 9) * r ^ 5 +
    70 * (b8 / h ^ 8) * r ^ 4 - 35 * (b7 / h ^ 7) * r ^ 3 +
    15 * (b6 / h ^ 6) * r ^ 2 - 5 * (b5 / h ^ 5) * r + b4 / h ^ 4

/-- First residual of the degree-`7` row.  Equivalent to
`T - 2 α C - (7/4) β B - (3/2) γ A - (15/4) A C - (15/8) B²
- (45/16) L A B - α A² - (5/16) A³`
on the second-, third-, and fourth-face integrals. -/
def epsilonResidual410 (L A B C0 P Q R T0 : F) : F :=
  T0 - (2 : F) * alphaResidual410 A P * C0 -
    (7 / 4 : F) * betaResidual410 L A B Q * B -
    (3 / 2 : F) * gammaResidual410 L A B C0 P R * A -
    (15 / 4 : F) * A * C0 - (15 / 8 : F) * B ^ 2 -
    (45 / 16 : F) * L * A * B -
    alphaResidual410 A P * A ^ 2 - (5 / 16 : F) * A ^ 3

/-- Polynomial numerator of `2048 h²⁰ ε` on the ninth-power face. -/
def localClearedSixthDefect410
    (h a3 a2 a1 a0 b8 b7 b6 b5 b4 : F[X]) (lambda : F) : F[X] :=
  (4096 : F[X]) * a3 ^ 4 * b8 -
    (6400 : F[X]) * a3 ^ 6 * h ^ 2 -
    (12288 : F[X]) * a2 * a3 ^ 2 * b8 * h ^ 4 -
    (3584 : F[X]) * a3 ^ 3 * b7 * h ^ 4 +
    (2304 : F[X]) * Polynomial.C lambda * a3 ^ 5 * h ^ 5 +
    (20480 : F[X]) * a2 * a3 ^ 4 * h ^ 6 +
    (3072 : F[X]) * a3 ^ 2 * b6 * h ^ 8 +
    (4096 : F[X]) * a2 ^ 2 * b8 * h ^ 8 +
    (7168 : F[X]) * a2 * a3 * b7 * h ^ 8 +
    (8192 : F[X]) * a1 * a3 * b8 * h ^ 8 -
    (9216 : F[X]) * Polynomial.C lambda * a2 * a3 ^ 3 * h ^ 9 -
    (14080 : F[X]) * a1 * a3 ^ 3 * h ^ 10 -
    (3840 : F[X]) * a2 ^ 2 * a3 ^ 2 * h ^ 10 -
    (2560 : F[X]) * a3 * b5 * h ^ 12 -
    (3072 : F[X]) * a2 * b6 * h ^ 12 -
    (3584 : F[X]) * a1 * b7 * h ^ 12 -
    (4096 : F[X]) * a0 * b8 * h ^ 12 +
    (6912 : F[X]) * Polynomial.C lambda * a1 * a3 ^ 2 * h ^ 13 +
    (6912 : F[X]) * Polynomial.C lambda * a2 ^ 2 * a3 * h ^ 13 -
    (5120 : F[X]) * a2 ^ 3 * h ^ 14 -
    (7680 : F[X]) * a1 * a2 * a3 * h ^ 14 +
    (7680 : F[X]) * a0 * a3 ^ 2 * h ^ 14 +
    (2048 : F[X]) * b4 * h ^ 16 -
    (4608 : F[X]) * Polynomial.C lambda * a0 * a3 * h ^ 17 -
    (4608 : F[X]) * Polynomial.C lambda * a1 * a2 * h ^ 17 +
    (10240 : F[X]) * a0 * a2 * h ^ 18 +
    (5120 : F[X]) * a1 ^ 2 * h ^ 18

/-- Mixed sixth-face combination `p₃² - 4 p₂ h⁴`. -/
def localSixthMixed410 (h a3 a2 : F[X]) : F[X] :=
  a3 ^ 2 - (4 : F[X]) * a2 * h ^ 4

/-- Exact denominator clearing for the decic `z⁴` coordinate on the
ninth-power face. -/
theorem depressedT410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 =
      (-525 * a3 ^ 6 * h ^ 2 + 126 * lambda * a3 ^ 5 * h ^ 5 +
          560 * a3 ^ 4 * b8 - 1120 * a3 ^ 3 * b7 * h ^ 4 +
          1920 * a3 ^ 2 * b6 * h ^ 8 - 2560 * a3 * b5 * h ^ 12 +
          2048 * b4 * h ^ 16) /
        (2048 * h ^ 20) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedT410, quarticDepressionR410, quarticDepressionR46]
  have hrewrite :
      210 * (a3 / (4 * h ^ 3)) ^ 6 -
          126 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 5 +
        70 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) ^ 4 -
          35 * (b7 / h ^ 7) * (a3 / (4 * h ^ 3)) ^ 3 +
        15 * (b6 / h ^ 6) * (a3 / (4 * h ^ 3)) ^ 2 -
          5 * (b5 / h ^ 5) * (a3 / (4 * h ^ 3)) + b4 / h ^ 4 =
        (-525 * a3 ^ 6 * h ^ 2 + 126 * lambda * a3 ^ 5 * h ^ 5 +
            560 * a3 ^ 4 * b8 - 1120 * a3 ^ 3 * b7 * h ^ 4 +
            1920 * a3 ^ 2 * b6 * h ^ 8 - 2560 * a3 * b5 * h ^ 12 +
            2048 * b4 * h ^ 16) /
          (2048 * h ^ 20) := by
    field_simp [hh, h2, h4, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh20,
      h2048]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh20,
      h2048]
    ring
  exact hrewrite

set_option maxHeartbeats 12000000 in
/-- Clearing the first integral
`T - 2 α C - (7/4) β B - (3/2) γ A - (15/4) A C - (15/8) B²
- (45/16) L A B - α A² - (5/16) A³`
against `h²⁰` on the ninth-power face. -/
theorem sixthDefect_eq_clearedEpsilon410
    (h a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (2048 : F) * h ^ 20 *
        epsilonResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6)
          (depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 b4) =
      (4096 : F) * a3 ^ 4 * b8 - (6400 : F) * a3 ^ 6 * h ^ 2 -
        (12288 : F) * a2 * a3 ^ 2 * b8 * h ^ 4 -
        (3584 : F) * a3 ^ 3 * b7 * h ^ 4 +
        (2304 : F) * lambda * a3 ^ 5 * h ^ 5 +
        (20480 : F) * a2 * a3 ^ 4 * h ^ 6 +
        (3072 : F) * a3 ^ 2 * b6 * h ^ 8 +
        (4096 : F) * a2 ^ 2 * b8 * h ^ 8 +
        (7168 : F) * a2 * a3 * b7 * h ^ 8 +
        (8192 : F) * a1 * a3 * b8 * h ^ 8 -
        (9216 : F) * lambda * a2 * a3 ^ 3 * h ^ 9 -
        (14080 : F) * a1 * a3 ^ 3 * h ^ 10 -
        (3840 : F) * a2 ^ 2 * a3 ^ 2 * h ^ 10 -
        (2560 : F) * a3 * b5 * h ^ 12 -
        (3072 : F) * a2 * b6 * h ^ 12 -
        (3584 : F) * a1 * b7 * h ^ 12 -
        (4096 : F) * a0 * b8 * h ^ 12 +
        (6912 : F) * lambda * a1 * a3 ^ 2 * h ^ 13 +
        (6912 : F) * lambda * a2 ^ 2 * a3 * h ^ 13 -
        (5120 : F) * a2 ^ 3 * h ^ 14 -
        (7680 : F) * a1 * a2 * a3 * h ^ 14 +
        (7680 : F) * a0 * a3 ^ 2 * h ^ 14 +
        (2048 : F) * b4 * h ^ 16 -
        (4608 : F) * lambda * a0 * a3 * h ^ 17 -
        (4608 : F) * lambda * a1 * a2 * h ^ 17 +
        (10240 : F) * a0 * a2 * h ^ 18 +
        (5120 : F) * a1 ^ 2 * h ^ 18 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hh12 : h ^ 12 ≠ 0 := pow_ne_zero 12 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh18 : h ^ 18 ≠ 0 := pow_ne_zero 18 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
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
  have hR :
      depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 =
        (-315 * a3 ^ 4 * h ^ 2 + 84 * lambda * a3 ^ 3 * h ^ 5 +
            224 * a3 ^ 2 * b8 - 224 * a3 * b7 * h ^ 4 +
            128 * b6 * h ^ 8) / (128 * h ^ 14) :=
    depressedR410_eq_cleared h a3 b9 b8 b7 b6 lambda hh hN
  have hT :
      depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 =
        (-525 * a3 ^ 6 * h ^ 2 + 126 * lambda * a3 ^ 5 * h ^ 5 +
            560 * a3 ^ 4 * b8 - 1120 * a3 ^ 3 * b7 * h ^ 4 +
            1920 * a3 ^ 2 * b6 * h ^ 8 - 2560 * a3 * b5 * h ^ 12 +
            2048 * b4 * h ^ 16) / (2048 * h ^ 20) :=
    depressedT410_eq_cleared h a3 b9 b8 b7 b6 b5 b4 lambda hh hN
  have h2048T :
      (2048 : F) * h ^ 20 *
          depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 b4 =
        -(525 : F) * a3 ^ 6 * h ^ 2 + (126 : F) * lambda * a3 ^ 5 * h ^ 5 +
          (560 : F) * a3 ^ 4 * b8 - (1120 : F) * a3 ^ 3 * b7 * h ^ 4 +
          (1920 : F) * a3 ^ 2 * b6 * h ^ 8 -
          (2560 : F) * a3 * b5 * h ^ 12 + (2048 : F) * b4 * h ^ 16 := by
    rw [hT]
    field_simp [hh, h2048, hh20]
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
  have h16P :
      (16 : F) * h ^ 8 *
          depressedP410 h (quarticDepressionR410 h a3) b9 b8 =
        (16 : F) * b8 - (45 : F) * a3 ^ 2 * h ^ 2 +
          (18 : F) * lambda * a3 * h ^ 5 := by
    rw [hP]
    field_simp [hh, h16, hh8pow]
    try ring
  have h8Q :
      (8 : F) * h ^ 11 *
          depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 =
        (30 : F) * a3 ^ 3 * h ^ 2 - (9 : F) * lambda * a3 ^ 2 * h ^ 5 -
          (16 : F) * a3 * b8 + (8 : F) * b7 * h ^ 4 := by
    rw [hQ]
    field_simp [hh, h8, hh11]
    try ring
  have h128R :
      (128 : F) * h ^ 14 *
          depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 =
        -(315 : F) * a3 ^ 4 * h ^ 2 + (84 : F) * lambda * a3 ^ 3 * h ^ 5 +
          (224 : F) * a3 ^ 2 * b8 - (224 : F) * a3 * b7 * h ^ 4 +
          (128 : F) * b6 * h ^ 8 := by
    rw [hR]
    field_simp [hh, h128, hh14]
    try ring
  have h4096PC :
      (4096 : F) * h ^ 20 *
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
              a0) =
        ((16 : F) * h ^ 8 *
            depressedP410 h (quarticDepressionR410 h a3) b9 b8) *
          ((256 : F) * h ^ 12 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
              a0) := by
    ring
  have h56QB :
      (3584 : F) * h ^ 20 *
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) =
        (56 : F) *
          ((8 : F) * h ^ 11 *
              depressedQ410 h (quarticDepressionR410 h a3) b9 b8
                b7) *
            ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) := by
    ring
  have h3RA :
      (3072 : F) * h ^ 20 *
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7
              b6 *
            depressedA410 h (quarticDepressionR410 h a3) a3 a2) =
        (3 : F) *
          ((128 : F) * h ^ 14 *
              depressedR410 h (quarticDepressionR410 h a3) b9 b8
                b7 b6) *
            ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3
                a2) := by
    ring
  have h4PA2 :
      (4096 : F) * h ^ 20 *
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^
              2) =
        (4 : F) *
          ((16 : F) * h ^ 8 *
              depressedP410 h (quarticDepressionR410 h a3) b9
                b8) *
            ((8 : F) * h ^ 6 *
                depressedA410 h (quarticDepressionR410 h a3) a3
                  a2) ^
              2 := by
    ring
  have h72LAB :
      (9216 : F) * h ^ 20 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
            depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) =
        (144 : F) * h ^ 5 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) *
            ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) := by
    ring
  have h5AC :
      (10240 : F) * h ^ 20 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
            depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
              a0) =
        (5 : F) * h ^ 2 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) *
            ((256 : F) * h ^ 12 *
              depressedC410 h (quarticDepressionR410 h a3) a3 a2
                a1 a0) := by
    ring
  have h80B2 :
      (5120 : F) * h ^ 20 *
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1) ^
            2 =
        (80 : F) * h ^ 2 *
          ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) ^
            2 := by
    field_simp [hh, h8, hh9, hh20]
    ring
  have h10A3 :
      (5120 : F) * h ^ 20 *
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^ 3 =
        (10 : F) * h ^ 2 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3
                a2) ^
            3 := by
    field_simp [hh, h8, hh6, hh20]
    ring
  have hdiff :
      (2048 : F) * h ^ 20 *
          epsilonResidual410
            (depressedL410 h (quarticDepressionR410 h a3) b9)
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
            (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
              a0)
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
            (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
            (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7
              b6)
            (depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7
              b6 b5 b4) =
        (2048 : F) * h ^ 20 *
            depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7
              b6 b5 b4 -
          (4096 : F) * h ^ 20 *
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
              depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
                a0) -
          (3584 : F) * h ^ 20 *
            (depressedQ410 h (quarticDepressionR410 h a3) b9 b8
                b7 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) -
          (3072 : F) * h ^ 20 *
            (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7
                b6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) +
          (4096 : F) * h ^ 20 *
            (depressedP410 h (quarticDepressionR410 h a3) b9 b8 *
              (depressedA410 h (quarticDepressionR410 h a3) a3
                  a2) ^
                2) +
          (9216 : F) * h ^ 20 *
            ((-lambda / 2 : F) *
              (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
                depressedB410 h (quarticDepressionR410 h a3) a3 a2
                  a1)) +
          (10240 : F) * h ^ 20 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
              depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1
                a0) +
          (5120 : F) * h ^ 20 *
            (depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) ^
              2 -
          (5120 : F) * h ^ 20 *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2) ^
              3 := by
    simp only [epsilonResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, hL]
    field_simp [h2, h4, h8, h16]
    ring
  have h9216L :
      (9216 : F) * h ^ 20 *
          ((-lambda / 2 : F) *
            (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1)) =
        -(72 : F) * lambda * h ^ 5 *
          ((8 : F) * h ^ 6 *
              depressedA410 h (quarticDepressionR410 h a3) a3 a2) *
            ((8 : F) * h ^ 9 *
              depressedB410 h (quarticDepressionR410 h a3) a3 a2
                a1) := by
    have hscale :
        (9216 : F) * h ^ 20 *
            ((-lambda / 2 : F) *
              (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
                depressedB410 h (quarticDepressionR410 h a3) a3 a2
                  a1)) =
          (-lambda / 2 : F) *
            ((9216 : F) * h ^ 20 *
              (depressedA410 h (quarticDepressionR410 h a3) a3 a2 *
                depressedB410 h (quarticDepressionR410 h a3) a3 a2
                  a1)) := by
      ring
    rw [hscale, h72LAB]
    field_simp [h2]
    ring
  rw [hdiff, h2048T, h4096PC, h16P, h256C, h56QB, h8Q, h8B, h3RA, h128R,
    h8A, h4PA2, h16P, h8A, h9216L, h8A, h8B, h5AC, h8A, h256C, h80B2,
    h8B, h10A3, h8A]
  ring

end Depression410Sixth

/-! ## Degree-`7` depressed Jacobian coefficient -/

section DepressedRow410Sixth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`7` Jacobian coefficient is
exactly `8 P C' + 7 Q B' + 6 R A' - B Q' - 2 A R' - 4 T'`. -/
theorem differentialJacobian_coeff_7_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 7 =
      (8 : F) * g.coeff 8 * d (f.coeff 0) +
        (7 : F) * g.coeff 7 * d (f.coeff 1) +
        (6 : F) * g.coeff 6 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 7) -
          (2 : F) * f.coeff 2 * d (g.coeff 6) -
          (4 : F) * d (g.coeff 4) := by
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
  have hmem07 : ((0, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem16 : ((1, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem25 : ((2, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem34 : ((3, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 7 =
        (8 : F) * g.coeff 8 * d (f.coeff 0) +
          (7 : F) * g.coeff 7 * d (f.coeff 1) +
          (6 : F) * g.coeff 6 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne02 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne12 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hsubset : ({(0, 7), (1, 6), (2, 5)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem07
      · subst b
        exact hmem16
      · subst b
        exact hmem25
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne07 : b ≠ (0, 7) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne16 : b ≠ (1, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne25 : b ≠ (2, 5) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne07
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne16
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne25
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 5 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
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
      coeff_coefficientDeriv, hder7, hder6, hder5]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 7 =
        f.coeff 1 * d (g.coeff 7) +
          (2 : F) * f.coeff 2 * d (g.coeff 6) +
          (4 : F) * d (g.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne07_16 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne07_34 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne16_34 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hsubset : ({(0, 7), (1, 6), (3, 4)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b
        exact hmem07
      · subst b
        exact hmem16
      · subst b
        exact hmem34
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (3, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne07 : b ≠ (0, 7) := by
        intro hEq
        subst b
        exact hbnot (Finset.mem_insert_self _ _)
      have hne16 : b ≠ (1, 6) := by
        intro hEq
        subst b
        exact hbnot (by simp)
      have hne34 : b ≠ (3, 4) := by
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
            apply hne07
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne16
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne34
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (3, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 4 := by
      rw [Finset.sum_insert (by simp [hne07_16, hne07_34]),
        Finset.sum_insert (by simp [hne16_34]), Finset.sum_singleton]
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

theorem epsilonResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q R T0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hgamma : d (gammaResidual410 L A B C0 P R) = 0)
    (hrow : (8 : F) * P * d C0 + (7 : F) * Q * d B +
        (6 : F) * R * d A - B * d Q - (2 : F) * A * d R -
        (4 : F) * d T0 = 0) :
    d (epsilonResidual410 L A B C0 P Q R T0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h7]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h92 : d (9 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h9]
  have h154 : d (15 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h15]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h15]
  have h4516 : d (45 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h45]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
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
  have hsqA : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hcube : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]
    ring
  have hR0 :
      d R - (5 / 2 : F) * d C0 - (9 / 4 : F) * L * d B -
          (2 : F) * A * d P - (2 : F) * P * d A +
          (25 / 4 : F) * A * d A = 0 := by
    have hexp :
        gammaResidual410 L A B C0 P R =
          R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A) := by
      simp only [gammaResidual410, pow_two]
    have hdg :
        d (R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A)) = 0 := by
      simpa [hexp] using hgamma
    simp [map_sub, map_add, Derivation.leibniz, h2, h52, h94, h258, hL,
      hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hexp :
      epsilonResidual410 L A B C0 P Q R T0 =
        T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
          (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
          (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
          (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A) := by
    simp only [epsilonResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, pow_two, pow_three]
    ring
  have hPderiv : d P = (5 / 2 : F) * d A := by
    linear_combination hP0
  have hQderiv : d Q = (5 / 2 : F) * d B + (9 / 4 : F) * L * d A := by
    linear_combination hQ0
  have hRderiv :
      d R = (5 / 2 : F) * d C0 + (9 / 4 : F) * L * d B +
        (5 : F) * A * d A + (2 : F) * P * d A -
        (25 / 4 : F) * A * d A := by
    linear_combination hR0 + (2 : F) * A * hP0
  have hTderiv :
      d T0 = (2 : F) * P * d C0 + (7 / 4 : F) * Q * d B +
        (3 / 2 : F) * R * d A - (1 / 4 : F) * B * d Q -
        (1 / 2 : F) * A * d R := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d T0 - (2 : F) * C0 * d P - (2 : F) * P * d C0 -
          (7 / 4 : F) * B * d Q - (7 / 4 : F) * Q * d B -
          (3 / 2 : F) * A * d R - (3 / 2 : F) * R * d A +
          (2 : F) * (A * A) * d P + (4 : F) * P * A * d A +
          (9 / 2 : F) * L * B * d A + (9 / 2 : F) * L * A * d B +
          (5 : F) * C0 * d A + (5 : F) * A * d C0 +
          (5 : F) * B * d B - (15 / 2 : F) * (A * A) * d A = 0 := by
    rw [hTderiv, hRderiv, hQderiv, hPderiv]
    ring
  rw [hexp]
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h8, h9, h16,
    h52, h74, h32, h92, h154, h158, h4516, h516, hL, hsqA, hsqB, hcube,
    zero_mul, add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Sixth

/-! ## Affine depression of a degree-ten source, `z⁴` coefficient -/

section AffineDecic410Sixth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁴` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff4_410
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

end AffineDecic410Sixth

/-! ## Local scalar identity at a simple root -/

section SixthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The fifth-face jet reduces `M`, `T`, `U`, `V`, and `W` to a finite
scalar system in `(t₁, p₂, s₂, v₃, w₇, q₅)`.  That system forces the
mixed relation `t₁² - 4 p₂ = 0` and does not force any individual
vanishing. -/
theorem sixthFace_rootMixed_410
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
        (6144 : F) * t1 * w7 = 0)
    (hW : -(5120 : F) * a2 ^ 3 + (4096 : F) * a2 ^ 2 * s2 -
        (3840 : F) * a2 ^ 2 * t1 ^ 2 - (12288 : F) * a2 * s2 * t1 ^ 2 +
        (20480 : F) * a2 * t1 ^ 4 + (7168 : F) * a2 * t1 * v3 -
        (3072 : F) * a2 * w7 - (2560 : F) * b5 * t1 +
        (4096 : F) * s2 * t1 ^ 4 - (6400 : F) * t1 ^ 6 -
        (3584 : F) * t1 ^ 3 * v3 + (3072 : F) * t1 ^ 2 * w7 = 0) :
    t1 ^ 2 - (4 : F) * a2 = 0 := by
  have hid :
      (8 : F) *
            (-(5120 : F) * a2 ^ 3 + (4096 : F) * a2 ^ 2 * s2 -
              (3840 : F) * a2 ^ 2 * t1 ^ 2 -
              (12288 : F) * a2 * s2 * t1 ^ 2 +
              (20480 : F) * a2 * t1 ^ 4 + (7168 : F) * a2 * t1 * v3 -
              (3072 : F) * a2 * w7 - (2560 : F) * b5 * t1 +
              (4096 : F) * s2 * t1 ^ 4 - (6400 : F) * t1 ^ 6 -
              (3584 : F) * t1 ^ 3 * v3 + (3072 : F) * t1 ^ 2 * w7) +
          (2048 : F) * a2 ^ 2 *
            ((8 : F) * s2 - (20 : F) * a2 - (15 : F) * t1 ^ 2) +
        ((336 : F) * a2 * t1 - (14 : F) * t1 ^ 3) *
            ((64 : F) * v3 - (128 : F) * s2 * t1 +
              (220 : F) * t1 ^ 3 + (80 : F) * a2 * t1) +
          ((192 : F) * a2 + (48 : F) * t1 ^ 2) *
            ((128 : F) * w7 - (224 : F) * t1 * v3 +
              (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
              (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
              (400 : F) * a2 ^ 2) +
        (5 : F) * t1 *
            ((4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
              (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
              (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
              (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
              (6144 : F) * t1 * w7) =
        (80 : F) * (t1 ^ 2 - (4 : F) * a2) ^ 3 := by
    ring
  have hleft :
      (8 : F) *
            (-(5120 : F) * a2 ^ 3 + (4096 : F) * a2 ^ 2 * s2 -
              (3840 : F) * a2 ^ 2 * t1 ^ 2 -
              (12288 : F) * a2 * s2 * t1 ^ 2 +
              (20480 : F) * a2 * t1 ^ 4 + (7168 : F) * a2 * t1 * v3 -
              (3072 : F) * a2 * w7 - (2560 : F) * b5 * t1 +
              (4096 : F) * s2 * t1 ^ 4 - (6400 : F) * t1 ^ 6 -
              (3584 : F) * t1 ^ 3 * v3 + (3072 : F) * t1 ^ 2 * w7) +
          (2048 : F) * a2 ^ 2 *
            ((8 : F) * s2 - (20 : F) * a2 - (15 : F) * t1 ^ 2) +
        ((336 : F) * a2 * t1 - (14 : F) * t1 ^ 3) *
            ((64 : F) * v3 - (128 : F) * s2 * t1 +
              (220 : F) * t1 ^ 3 + (80 : F) * a2 * t1) +
          ((192 : F) * a2 + (48 : F) * t1 ^ 2) *
            ((128 : F) * w7 - (224 : F) * t1 * v3 +
              (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
              (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
              (400 : F) * a2 ^ 2) +
        (5 : F) * t1 *
            ((4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
              (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
              (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
              (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
              (6144 : F) * t1 * w7) =
        0 := by
    linear_combination (8 : F) * hW + (2048 : F) * a2 ^ 2 * hM +
      ((336 : F) * a2 * t1 - (14 : F) * t1 ^ 3) * hT +
      ((192 : F) * a2 + (48 : F) * t1 ^ 2) * hU + (5 : F) * t1 * hV
  have h80 : (80 : F) ≠ 0 := by norm_num
  have hpow :
      (80 : F) * (t1 ^ 2 - (4 : F) * a2) ^ 3 = 0 :=
    hid.symm.trans hleft
  have hcube : (t1 ^ 2 - (4 : F) * a2) ^ 3 = 0 :=
    (mul_eq_zero.mp hpow).resolve_left h80
  have hlin :
      (t1 ^ 2 - (4 : F) * a2) * (t1 ^ 2 - (4 : F) * a2) ^ 2 = 0 := by
    simpa [pow_succ] using hcube
  rcases mul_eq_zero.mp hlin with hx | hsq
  · exact hx
  · have hlin2 :
        (t1 ^ 2 - (4 : F) * a2) * (t1 ^ 2 - (4 : F) * a2) = 0 := by
      simpa [pow_two] using hsq
    exact (mul_eq_zero.mp hlin2).elim id id

set_option maxHeartbeats 8000000 in
/-- The sixth defect on the fourth-face jet is `h¹⁴` times an explicit
polynomial whose constant term is the scalar combination `W₀`. -/
theorem sixthDefect_onFourthJet_410
    (h t1 a2 a1 a0 s2 v3 w7 b5 b4 : F[X]) (lambda : F) :
    localClearedSixthDefect410 h (h ^ 2 * t1) a2 a1 a0
        (h ^ 6 * s2) (h ^ 4 * v3) (h ^ 2 * w7) b5 b4 lambda =
      h ^ 14 *
        (-(5120 : F[X]) * a2 ^ 3 + (4096 : F[X]) * a2 ^ 2 * s2 -
          (3840 : F[X]) * a2 ^ 2 * t1 ^ 2 -
          (12288 : F[X]) * a2 * s2 * t1 ^ 2 +
          (20480 : F[X]) * a2 * t1 ^ 4 +
          (7168 : F[X]) * a2 * t1 * v3 -
          (3072 : F[X]) * a2 * w7 - (2560 : F[X]) * b5 * t1 +
          (4096 : F[X]) * s2 * t1 ^ 4 - (6400 : F[X]) * t1 ^ 6 -
          (3584 : F[X]) * t1 ^ 3 * v3 +
          (3072 : F[X]) * t1 ^ 2 * w7 +
          (6912 : F[X]) * Polynomial.C lambda * a2 ^ 2 * t1 * h -
          (9216 : F[X]) * Polynomial.C lambda * a2 * t1 ^ 3 * h +
          (2304 : F[X]) * Polynomial.C lambda * t1 ^ 5 * h -
          (7680 : F[X]) * a1 * a2 * t1 * h ^ 2 +
          (8192 : F[X]) * a1 * s2 * t1 * h ^ 2 -
          (14080 : F[X]) * a1 * t1 ^ 3 * h ^ 2 -
          (3584 : F[X]) * a1 * v3 * h ^ 2 +
          (2048 : F[X]) * b4 * h ^ 2 -
          (4608 : F[X]) * Polynomial.C lambda * a1 * a2 * h ^ 3 +
          (6912 : F[X]) * Polynomial.C lambda * a1 * t1 ^ 2 * h ^ 3 +
          (10240 : F[X]) * a0 * a2 * h ^ 4 -
          (4096 : F[X]) * a0 * s2 * h ^ 4 +
          (7680 : F[X]) * a0 * t1 ^ 2 * h ^ 4 +
          (5120 : F[X]) * a1 ^ 2 * h ^ 4 -
          (4608 : F[X]) * Polynomial.C lambda * a0 * t1 * h ^ 5) := by
  simp only [localClearedSixthDefect410]
  ring

end SixthFaceScalars410

/-! ## Source-facing sixth-face packet -/

section NonzeroSixthFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The fifth quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²⁰`. -/
theorem nonzeroFace410_sixthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ zeta : k,
      localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 20 := by
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
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
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
  have hg6 :
      g.coeff 6 =
        depressedR410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedR410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg4 :
      g.coeff 4 =
        depressedT410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedT410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
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
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
          (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
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
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow9)
  have heps0 :
      ratFuncDerivation68
        (epsilonResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4)) = 0 :=
    epsilonResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 4) hLconst halpha0 hbeta0 hgamma0
      (by simpa using hrow7)
  obtain ⟨zeta0, hzeta0⟩ :
      ∃ a : k,
        epsilonResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 4) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using heps0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda) =
        (2048 : RatFunc k) * hRF ^ 20 *
          epsilonResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 4) := by
    have hF := sixthDefect_eq_clearedEpsilon410 hRF a3 a2 a1 a0 b9 b8 b7
      b6 b5 b4 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedSixthDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b8,
      b7, b6, b5, b4, epsilonResidual410, alphaResidual410,
      betaResidual410, gammaResidual410, hf2, hf1, hf0, hg4, hg6, hg7,
      hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (2048 * zeta0) * h0 ^ 20) := by
    rw [hclear, hzeta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨2048 * zeta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

set_option maxHeartbeats 12000000 in
/-- Finite local initial packet: the fifth-face jet together with the
degree-`7` defect forces the mixed divisibility
`h⁵ ∣ p₃² - 4 p₂ h⁴`
at the degree-one root. -/
theorem nonzeroFace410_linearRoot_sixthInitialPacket
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
        (q.coeff 5) ∧
      h0 ^ 5 ∣ localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) := by
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
  obtain ⟨zeta, hW⟩ :=
    nonzeroFace410_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨hp3pow, hq8pow, hq7pow, hq6pow, hq9pow, hmix5⟩ :=
    nonzeroFace410_linearRoot_fifthInitialPacket p q H h0 j lambda a
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
  have hW0 :
      -(5120 : k[X]) * p.coeff 2 ^ 3 +
          (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
        (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
          (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
        (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
          (7168 : k[X]) * p.coeff 2 * t1 * v3 -
        (3072 : k[X]) * p.coeff 2 * w7 -
          (2560 : k[X]) * q.coeff 5 * t1 +
        (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
          (3584 : k[X]) * t1 ^ 3 * v3 +
        (3072 : k[X]) * t1 ^ 2 * w7 +
          (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 * t1 *
            h0 -
        (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 * t1 ^ 3 *
            h0 +
          (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 * h0 -
        (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 * h0 ^ 2 +
          (8192 : k[X]) * p.coeff 1 * s2 * t1 * h0 ^ 2 -
        (14080 : k[X]) * p.coeff 1 * t1 ^ 3 * h0 ^ 2 -
          (3584 : k[X]) * p.coeff 1 * v3 * h0 ^ 2 +
        (2048 : k[X]) * q.coeff 4 * h0 ^ 2 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 * p.coeff 2 *
            h0 ^ 3 +
        (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 * t1 ^ 2 *
            h0 ^ 3 +
          (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 4 -
        (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 4 +
          (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 4 +
        (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 4 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
            h0 ^ 5 =
        Polynomial.C zeta * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 14 hh0)
    calc
      h0 ^ 14 *
            (-(5120 : k[X]) * p.coeff 2 ^ 3 +
                (4096 : k[X]) * p.coeff 2 ^ 2 * s2 -
              (3840 : k[X]) * p.coeff 2 ^ 2 * t1 ^ 2 -
                (12288 : k[X]) * p.coeff 2 * s2 * t1 ^ 2 +
              (20480 : k[X]) * p.coeff 2 * t1 ^ 4 +
                (7168 : k[X]) * p.coeff 2 * t1 * v3 -
              (3072 : k[X]) * p.coeff 2 * w7 -
                (2560 : k[X]) * q.coeff 5 * t1 +
              (4096 : k[X]) * s2 * t1 ^ 4 - (6400 : k[X]) * t1 ^ 6 -
                (3584 : k[X]) * t1 ^ 3 * v3 +
              (3072 : k[X]) * t1 ^ 2 * w7 +
                (6912 : k[X]) * Polynomial.C lambda * p.coeff 2 ^ 2 *
                    t1 * h0 -
              (9216 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    t1 ^ 3 * h0 +
                (2304 : k[X]) * Polynomial.C lambda * t1 ^ 5 * h0 -
              (7680 : k[X]) * p.coeff 1 * p.coeff 2 * t1 * h0 ^ 2 +
                (8192 : k[X]) * p.coeff 1 * s2 * t1 * h0 ^ 2 -
              (14080 : k[X]) * p.coeff 1 * t1 ^ 3 * h0 ^ 2 -
                (3584 : k[X]) * p.coeff 1 * v3 * h0 ^ 2 +
              (2048 : k[X]) * q.coeff 4 * h0 ^ 2 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                    p.coeff 2 * h0 ^ 3 +
              (6912 : k[X]) * Polynomial.C lambda * p.coeff 1 *
                    t1 ^ 2 * h0 ^ 3 +
                (10240 : k[X]) * p.coeff 0 * p.coeff 2 * h0 ^ 4 -
              (4096 : k[X]) * p.coeff 0 * s2 * h0 ^ 4 +
                (7680 : k[X]) * p.coeff 0 * t1 ^ 2 * h0 ^ 4 +
              (5120 : k[X]) * p.coeff 1 ^ 2 * h0 ^ 4 -
                (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 * t1 *
                    h0 ^ 5) =
          localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda := by
        have hred :=
          sixthDefect_onFourthJet_410 h0 t1 (p.coeff 2) (p.coeff 1)
            (p.coeff 0) s2 v3 w7 (q.coeff 5) (q.coeff 4) lambda
        rw [← ht1, ← hs2, ← hv3, ← hw7] at hred
        exact hred.symm
      _ = Polynomial.C zeta * h0 ^ 20 := hW
      _ = h0 ^ 14 * (Polynomial.C zeta * h0 ^ 6) := by ring
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
  have hWroot :
      -(5120 : k) * ((p.coeff 2).eval a) ^ 3 +
          (4096 : k) * ((p.coeff 2).eval a) ^ 2 * s2.eval a -
        (3840 : k) * ((p.coeff 2).eval a) ^ 2 * (t1.eval a) ^ 2 -
          (12288 : k) * (p.coeff 2).eval a * s2.eval a *
            (t1.eval a) ^ 2 +
        (20480 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 4 +
          (7168 : k) * (p.coeff 2).eval a * t1.eval a * v3.eval a -
        (3072 : k) * (p.coeff 2).eval a * w7.eval a -
          (2560 : k) * (q.coeff 5).eval a * t1.eval a +
        (4096 : k) * s2.eval a * (t1.eval a) ^ 4 -
          (6400 : k) * (t1.eval a) ^ 6 -
        (3584 : k) * (t1.eval a) ^ 3 * v3.eval a +
          (3072 : k) * (t1.eval a) ^ 2 * w7.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hW0
    simpa [hroot] using heval
  have hmix6 :
      (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a = 0 :=
    sixthFace_rootMixed_410 (t1.eval a) ((p.coeff 2).eval a)
      (s2.eval a) (v3.eval a) (w7.eval a) ((q.coeff 5).eval a)
      hMroot hTroot hUroot hVroot hWroot
  have hform :
      localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) =
        h0 ^ 4 * (t1 ^ 2 - (4 : k[X]) * p.coeff 2) := by
    simp only [localSixthMixed410, ht1]
    ring
  have hjet0 : (t1 ^ 2 - (4 : k[X]) * p.coeff 2).eval a = 0 := by
    have heval :
        (t1 ^ 2 - (4 : k[X]) * p.coeff 2).eval a =
          (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a := by
      simp [eval_pow]
    rw [heval]
    linear_combination hmix6
  have hjetdiv : h0 ∣ t1 ^ 2 - (4 : k[X]) * p.coeff 2 :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0
      (t1 ^ 2 - (4 : k[X]) * p.coeff 2) a hh0degree hroot hjet0
  obtain ⟨rQ, hrQ⟩ := hjetdiv
  refine ⟨⟨t1, ht1⟩, ⟨s2, hs2⟩, ⟨v3, hv3⟩, ⟨w7, hw7⟩, hq9pow, hmix5,
    ⟨rQ, ?_⟩⟩
  rw [hform, hrQ]
  ring

/-- Source-facing sixth integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_sixthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda zeta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
          Polynomial.C zeta * h0 ^ 20 := by
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
  obtain ⟨zeta, hW⟩ :=
    nonzeroFace410_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, zeta, hh0, hlambda, hh0degree, hH, hN', hW⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the fifth-face jet together with the mixed relation
`h⁵ ∣ p₃² - 4 p₂ h⁴`. -/
theorem normalized410ScaleTwo_nonzeroFace_sixthInitialPacket
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
        h0 ^ 5 ∣ localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) ∧
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
  obtain ⟨hp3, hq8, hq7, hq6, hq9, hmix5, hmix6⟩ :=
    nonzeroFace410_linearRoot_sixthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq6, hq9, hmix5, hmix6, hN'⟩

end NonzeroSixthFace410

#print axioms sixthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_7_monicQuarticDecic
#print axioms sixthDefect_eq_clearedEpsilon410
#print axioms sixthFace_rootMixed_410
#print axioms sixthDefect_onFourthJet_410
#print axioms nonzeroFace410_sixthDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_sixthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_sixthDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_sixthInitialPacket

end Max11DegreeRoutes
