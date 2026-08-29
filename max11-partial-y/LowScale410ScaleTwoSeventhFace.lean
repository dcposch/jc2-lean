import LowScale410ScaleTwoSixthFace

/-! # Scale-two seventh face for normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the sixth face supplies the degree-`7` integral and
the jet `h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`, `h⁸ ∣ q₉` together
with `h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸ - 256 q₅ h¹⁰` and
`h⁵ ∣ p₃² - 4 p₂ h⁴`.  The next Keller coefficient is the degree-`6`
Jacobian row.  After the same quartic depression that kills `z³`, that
row is `7 Q C' + 6 R B' + 5 S A' - B R' - 2 A S' - 4 U' = 0`.  The
resulting first integral clears to a polynomial defect `X` of weight
twenty-three.

Evaluating the second through fifth defects together with the sixth-face
mixed relation at the root of `h` forces the one-parameter jet
`2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`, `16 (q₆/h²)(a) = 5 t₁⁴`,
and `32 q₅(a) = t₁⁵` on `p₃ = t₁ h²` and `4 p₂(a) = t₁²`.  The degree-`6`
defect is compatible with that jet and does not force `t₁(a) = 0`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z⁰`/`z³` defect after the degree-`7` integral. -/
theorem seventhCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC2]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z³` coordinates -/

section Depression410Seventh

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z³` coefficient. -/
def depressedU410 (h r b9 b8 b7 b6 b5 b4 b3 : F) : F :=
  -120 * r ^ 7 + 84 * (b9 / h ^ 9) * r ^ 6 -
    56 * (b8 / h ^ 8) * r ^ 5 + 35 * (b7 / h ^ 7) * r ^ 4 -
    20 * (b6 / h ^ 6) * r ^ 3 + 10 * (b5 / h ^ 5) * r ^ 2 -
    4 * (b4 / h ^ 4) * r + b3 / h ^ 3

/-- First residual of the degree-`6` row.  Equivalent to
`U - (7/4) β C - (3/2) γ B - (5/4) δ A - (15/4) B C - (15/16) A² B
- (45/16) L A C - (45/32) L B² - (15/128) L A³ - 2 α A B
- (21/32) β A²`
on the second-, third-, fourth-, and fifth-face integrals. -/
def zetaResidual410 (L A B C0 P Q R S0 U0 : F) : F :=
  U0 - (7 / 4 : F) * betaResidual410 L A B Q * C0 -
    (3 / 2 : F) * gammaResidual410 L A B C0 P R * B -
    (5 / 4 : F) * deltaResidual410 L A B C0 P Q S0 * A -
    (15 / 4 : F) * B * C0 - (15 / 16 : F) * A ^ 2 * B -
    (45 / 16 : F) * L * A * C0 - (45 / 32 : F) * L * B ^ 2 -
    (15 / 128 : F) * L * A ^ 3 -
    (2 : F) * alphaResidual410 A P * A * B -
    (21 / 32 : F) * betaResidual410 L A B Q * A ^ 2

/-- Polynomial numerator of `131072 h²³ ζ` on the ninth-power face. -/
def localClearedSeventhDefect410
    (h a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : F[X]) (lambda : F) : F[X] :=
  (288420 : F[X]) * a3 ^ 7 * h ^ 2 -
    (100947 : F[X]) * Polynomial.C lambda * a3 ^ 6 * h ^ 5 -
    (1287440 : F[X]) * a2 * a3 ^ 5 * h ^ 6 -
    (187264 : F[X]) * a3 ^ 5 * b8 +
    (526680 : F[X]) * Polynomial.C lambda * a2 * a3 ^ 4 * h ^ 9 +
    (1047200 : F[X]) * a1 * a3 ^ 4 * h ^ 10 +
    (172480 : F[X]) * a3 ^ 4 * b7 * h ^ 4 +
    (985600 : F[X]) * a2 ^ 2 * a3 ^ 3 * h ^ 10 +
    (788480 : F[X]) * a2 * a3 ^ 3 * b8 * h ^ 4 -
    (443520 : F[X]) * Polynomial.C lambda * a1 * a3 ^ 3 * h ^ 13 -
    (788480 : F[X]) * a0 * a3 ^ 3 * h ^ 14 -
    (157696 : F[X]) * a3 ^ 3 * b6 * h ^ 8 -
    (665280 : F[X]) * Polynomial.C lambda * a2 ^ 2 * a3 ^ 2 * h ^ 13 -
    (591360 : F[X]) * a1 * a2 * a3 ^ 2 * h ^ 14 -
    (551936 : F[X]) * a2 * a3 ^ 2 * b7 * h ^ 8 -
    (630784 : F[X]) * a1 * a3 ^ 2 * b8 * h ^ 8 +
    (354816 : F[X]) * Polynomial.C lambda * a0 * a3 ^ 2 * h ^ 17 +
    (143360 : F[X]) * a3 ^ 2 * b5 * h ^ 12 +
    (394240 : F[X]) * a2 ^ 3 * a3 * h ^ 14 -
    (630784 : F[X]) * a2 ^ 2 * a3 * b8 * h ^ 8 +
    (709632 : F[X]) * Polynomial.C lambda * a1 * a2 * a3 * h ^ 17 -
    (286720 : F[X]) * a0 * a2 * a3 * h ^ 18 +
    (344064 : F[X]) * a2 * a3 * b6 * h ^ 12 -
    (143360 : F[X]) * a1 ^ 2 * a3 * h ^ 18 +
    (401408 : F[X]) * a1 * a3 * b7 * h ^ 12 +
    (458752 : F[X]) * a0 * a3 * b8 * h ^ 12 -
    (131072 : F[X]) * a3 * b4 * h ^ 16 +
    (118272 : F[X]) * Polynomial.C lambda * a2 ^ 3 * h ^ 17 -
    (788480 : F[X]) * a1 * a2 ^ 2 * h ^ 18 +
    (200704 : F[X]) * a2 ^ 2 * b7 * h ^ 12 +
    (458752 : F[X]) * a1 * a2 * b8 * h ^ 12 -
    (258048 : F[X]) * Polynomial.C lambda * a0 * a2 * h ^ 21 -
    (163840 : F[X]) * a2 * b5 * h ^ 16 -
    (129024 : F[X]) * Polynomial.C lambda * a1 ^ 2 * h ^ 21 +
    (573440 : F[X]) * a0 * a1 * h ^ 22 -
    (196608 : F[X]) * a1 * b6 * h ^ 16 -
    (229376 : F[X]) * a0 * b7 * h ^ 16 +
    (131072 : F[X]) * b3 * h ^ 20

/-- Exact denominator clearing for the decic `z³` coordinate on the
ninth-power face. -/
theorem depressedU410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedU410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 b3 =
      (90 * a3 ^ 7 * h ^ 2 - 21 * lambda * a3 ^ 6 * h ^ 5 -
          112 * a3 ^ 5 * b8 + 280 * a3 ^ 4 * b7 * h ^ 4 -
          640 * a3 ^ 3 * b6 * h ^ 8 + 1280 * a3 ^ 2 * b5 * h ^ 12 -
          2048 * a3 * b4 * h ^ 16 + 2048 * b3 * h ^ 20) /
        (2048 * h ^ 23) := by
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
  have hh23 : h ^ 23 ≠ 0 := pow_ne_zero 23 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedU410, quarticDepressionR410, quarticDepressionR46]
  have hrewrite :
      -120 * (a3 / (4 * h ^ 3)) ^ 7 +
          84 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 6 -
        56 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) ^ 5 +
          35 * (b7 / h ^ 7) * (a3 / (4 * h ^ 3)) ^ 4 -
        20 * (b6 / h ^ 6) * (a3 / (4 * h ^ 3)) ^ 3 +
          10 * (b5 / h ^ 5) * (a3 / (4 * h ^ 3)) ^ 2 -
        4 * (b4 / h ^ 4) * (a3 / (4 * h ^ 3)) + b3 / h ^ 3 =
        (90 * a3 ^ 7 * h ^ 2 - 21 * lambda * a3 ^ 6 * h ^ 5 -
            112 * a3 ^ 5 * b8 + 280 * a3 ^ 4 * b7 * h ^ 4 -
            640 * a3 ^ 3 * b6 * h ^ 8 + 1280 * a3 ^ 2 * b5 * h ^ 12 -
            2048 * a3 * b4 * h ^ 16 + 2048 * b3 * h ^ 20) /
          (2048 * h ^ 23) := by
    field_simp [hh, h2, h4, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh23,
      h2048]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh23,
      h2048]
    ring
  exact hrewrite

set_option maxHeartbeats 16000000 in
/-- Clearing the first integral
`U - (7/4) β C - (3/2) γ B - (5/4) δ A - (15/4) B C - (15/16) A² B
- (45/16) L A C - (45/32) L B² - (15/128) L A³ - 2 α A B
- (21/32) β A²`
against `h²³` on the ninth-power face. -/
theorem seventhDefect_eq_clearedZeta410
    (h a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (131072 : F) * h ^ 23 *
        zetaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6)
          (depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5)
          (depressedU410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 b4 b3) =
      (288420 : F) * a3 ^ 7 * h ^ 2 -
        (100947 : F) * lambda * a3 ^ 6 * h ^ 5 -
        (1287440 : F) * a2 * a3 ^ 5 * h ^ 6 -
        (187264 : F) * a3 ^ 5 * b8 +
        (526680 : F) * lambda * a2 * a3 ^ 4 * h ^ 9 +
        (1047200 : F) * a1 * a3 ^ 4 * h ^ 10 +
        (172480 : F) * a3 ^ 4 * b7 * h ^ 4 +
        (985600 : F) * a2 ^ 2 * a3 ^ 3 * h ^ 10 +
        (788480 : F) * a2 * a3 ^ 3 * b8 * h ^ 4 -
        (443520 : F) * lambda * a1 * a3 ^ 3 * h ^ 13 -
        (788480 : F) * a0 * a3 ^ 3 * h ^ 14 -
        (157696 : F) * a3 ^ 3 * b6 * h ^ 8 -
        (665280 : F) * lambda * a2 ^ 2 * a3 ^ 2 * h ^ 13 -
        (591360 : F) * a1 * a2 * a3 ^ 2 * h ^ 14 -
        (551936 : F) * a2 * a3 ^ 2 * b7 * h ^ 8 -
        (630784 : F) * a1 * a3 ^ 2 * b8 * h ^ 8 +
        (354816 : F) * lambda * a0 * a3 ^ 2 * h ^ 17 +
        (143360 : F) * a3 ^ 2 * b5 * h ^ 12 +
        (394240 : F) * a2 ^ 3 * a3 * h ^ 14 -
        (630784 : F) * a2 ^ 2 * a3 * b8 * h ^ 8 +
        (709632 : F) * lambda * a1 * a2 * a3 * h ^ 17 -
        (286720 : F) * a0 * a2 * a3 * h ^ 18 +
        (344064 : F) * a2 * a3 * b6 * h ^ 12 -
        (143360 : F) * a1 ^ 2 * a3 * h ^ 18 +
        (401408 : F) * a1 * a3 * b7 * h ^ 12 +
        (458752 : F) * a0 * a3 * b8 * h ^ 12 -
        (131072 : F) * a3 * b4 * h ^ 16 +
        (118272 : F) * lambda * a2 ^ 3 * h ^ 17 -
        (788480 : F) * a1 * a2 ^ 2 * h ^ 18 +
        (200704 : F) * a2 ^ 2 * b7 * h ^ 12 +
        (458752 : F) * a1 * a2 * b8 * h ^ 12 -
        (258048 : F) * lambda * a0 * a2 * h ^ 21 -
        (163840 : F) * a2 * b5 * h ^ 16 -
        (129024 : F) * lambda * a1 ^ 2 * h ^ 21 +
        (573440 : F) * a0 * a1 * h ^ 22 -
        (196608 : F) * a1 * b6 * h ^ 16 -
        (229376 : F) * a0 * b7 * h ^ 16 +
        (131072 : F) * b3 * h ^ 20 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hh12 : h ^ 12 ≠ 0 := pow_ne_zero 12 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh17 : h ^ 17 ≠ 0 := pow_ne_zero 17 hh
  have hh23 : h ^ 23 ≠ 0 := pow_ne_zero 23 hh
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
  have hS :
      depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 =
        (252 * a3 ^ 5 * h ^ 2 - 63 * lambda * a3 ^ 4 * h ^ 5 -
            224 * a3 ^ 3 * b8 + 336 * a3 ^ 2 * b7 * h ^ 4 -
            384 * a3 * b6 * h ^ 8 + 256 * b5 * h ^ 12) /
          (256 * h ^ 17) :=
    depressedS410_eq_cleared h a3 b9 b8 b7 b6 b5 lambda hh hN
  have hU :
      depressedU410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
          b4 b3 =
        (90 * a3 ^ 7 * h ^ 2 - 21 * lambda * a3 ^ 6 * h ^ 5 -
            112 * a3 ^ 5 * b8 + 280 * a3 ^ 4 * b7 * h ^ 4 -
            640 * a3 ^ 3 * b6 * h ^ 8 + 1280 * a3 ^ 2 * b5 * h ^ 12 -
            2048 * a3 * b4 * h ^ 16 + 2048 * b3 * h ^ 20) /
          (2048 * h ^ 23) :=
    depressedU410_eq_cleared h a3 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  simp only [zetaResidual410, hL, hA, hB, hC, hP, hQ, hR, hS, hU,
    alphaResidual410, betaResidual410, gammaResidual410,
    deltaResidual410]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h2048, h131072,
    hh6, hh8pow, hh9, hh11, hh12, hh14, hh17, hh23]
  ring

end Depression410Seventh

/-! ## Degree-`6` depressed Jacobian coefficient -/

section DepressedRow410Seventh

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`6` Jacobian coefficient is
exactly `7 Q C' + 6 R B' + 5 S A' - B R' - 2 A S' - 4 U'`. -/
theorem differentialJacobian_coeff_6_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 6 =
      (7 : F) * g.coeff 7 * d (f.coeff 0) +
        (6 : F) * g.coeff 6 * d (f.coeff 1) +
        (5 : F) * g.coeff 5 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 6) -
          (2 : F) * f.coeff 2 * d (g.coeff 5) -
          (4 : F) * d (g.coeff 3) := by
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
  have hmem06 : ((0, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem15 : ((1, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem24 : ((2, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem33 : ((3, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 6 =
        (7 : F) * g.coeff 7 * d (f.coeff 0) +
          (6 : F) * g.coeff 6 * d (f.coeff 1) +
          (5 : F) * g.coeff 5 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne02 : ((0, 6) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hne12 : ((1, 5) : ℕ × ℕ) ≠ (2, 4) := by decide
    have hsubset : ({(0, 6), (1, 5), (2, 4)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem06
      · subst b; exact hmem15
      · subst b; exact hmem24
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (2, 4)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne06 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne15 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne24 : b ≠ (2, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne06
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne15
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne24
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (2, 4)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 4 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder6, hder5, hder4]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 6 =
        f.coeff 1 * d (g.coeff 6) +
          (2 : F) * f.coeff 2 * d (g.coeff 5) +
          (4 : F) * d (g.coeff 3) := by
    rw [Polynomial.coeff_mul]
    have hne06_15 : ((0, 6) : ℕ × ℕ) ≠ (1, 5) := by decide
    have hne06_33 : ((0, 6) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hne15_33 : ((1, 5) : ℕ × ℕ) ≠ (3, 3) := by decide
    have hsubset : ({(0, 6), (1, 5), (3, 3)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (6 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem06
      · subst b; exact hmem15
      · subst b; exact hmem33
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (6 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 6), (1, 5), (3, 3)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 6 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne06 : b ≠ (0, 6) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne15 : b ≠ (1, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne33 : b ≠ (3, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 4 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h2 : b.1 = 2
        · have hf2 : f.derivative.coeff b.1 = 0 := by
            rw [h2, Polynomial.coeff_derivative, hf3]
            simp
          simp [hf2]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne06
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne15
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne33
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 6), (1, 5), (3, 3)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 3 := by
      rw [Finset.sum_insert (by simp [hne06_15, hne06_33]),
        Finset.sum_insert (by simp [hne15_33]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : f.derivative.coeff 3 = (4 : F) := by
      rw [Polynomial.coeff_derivative, hf4]; norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder3]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem zetaResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q R S0 U0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hgamma : d (gammaResidual410 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual410 L A B C0 P Q S0) = 0)
    (hrow : (7 : F) * Q * d C0 + (6 : F) * R * d B +
        (5 : F) * S0 * d A - B * d R - (2 : F) * A * d S0 -
        (4 : F) * d U0 = 0) :
    d (zetaResidual410 L A B C0 P Q R S0 U0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h49 : d (49 : F) = 0 := d.map_natCast 49
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h231 : d (231 : F) = 0 := d.map_natCast 231
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h32div : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h7]
  have h72 : d (7 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h7]
  have h4932 : d (49 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h49]
  have h6316 : d (63 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h63]
  have h6332 : d (63 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h63]
  have h358 : d (35 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h35]
  have h231128 : d (231 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h231]
  have h38564 : d (385 / 64 : F) = 0 := by
    have h64 : d (64 : F) = 0 := d.map_natCast 64
    simp [Derivation.leibniz_div, h64, h385]
  have hP0 : d P - (5 / 2 : F) * d A = 0 := by
    simpa [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
      add_zero] using halpha
  have hQ0 : d Q - (5 / 2 : F) * d B - (9 / 4 : F) * L * d A = 0 := by
    simpa [betaResidual410, map_sub, Derivation.leibniz, h52, h94, hL,
      zero_mul, add_zero, mul_zero] using hbeta
  have hsqA : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]; ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]; ring
  have hcube : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hR0 :
      d R - (5 / 2 : F) * d C0 - (9 / 4 : F) * L * d B -
          (2 : F) * A * d P - (2 : F) * P * d A +
          (25 / 4 : F) * A * d A = 0 := by
    have hexp :
        gammaResidual410 L A B C0 P R =
          R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A) := by
      simp only [gammaResidual410, pow_two]
    have h258 : d (25 / 8 : F) = 0 := by
      have h25 : d (25 : F) = 0 := d.map_natCast 25
      simp [Derivation.leibniz_div, h8, h25]
    have hdg :
        d (R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A)) = 0 := by
      simpa [hexp] using hgamma
    simp [map_sub, map_add, Derivation.leibniz, h2, h52, h94, h258, hL,
      hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hS0 :
      d S0 - (9 / 4 : F) * L * d C0 - (2 : F) * B * d P -
          (2 : F) * P * d B - (7 / 4 : F) * A * d Q -
          (7 / 4 : F) * Q * d A + (45 / 8 : F) * B * d A +
          (45 / 8 : F) * A * d B + (81 / 16 : F) * L * A * d A = 0 := by
    have hexp :
        deltaResidual410 L A B C0 P Q S0 =
          S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A) := by
      simp only [deltaResidual410, alphaResidual410, betaResidual410,
        pow_two]
      ring
    have h458 : d (45 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h45]
    have h8132 : d (81 / 32 : F) = 0 := by
      have h81 : d (81 : F) = 0 := d.map_natCast 81
      simp [Derivation.leibniz_div, h32, h81]
    have hdg :
        d (S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A)) = 0 := by
      simpa [hexp] using hdelta
    simp [map_sub, map_add, Derivation.leibniz, h2, h94, h74, h458, h8132,
      hL, hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hexp :
      zetaResidual410 L A B C0 P Q R S0 U0 =
        U0 - (5 / 4 : F) * A * S0 - (3 / 2 : F) * B * R -
          (7 / 4 : F) * C0 * Q + (7 / 2 : F) * A * B * P +
          (49 / 32 : F) * (A * A) * Q + (63 / 16 : F) * L * A * C0 +
          (63 / 32 : F) * L * (B * B) + (35 / 8 : F) * B * C0 -
          (231 / 128 : F) * L * (A * A * A) -
          (385 / 64 : F) * (A * A) * B := by
    simp only [zetaResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, deltaResidual410, pow_two, pow_three]
    ring
  have hPderiv : d P = (5 / 2 : F) * d A := by linear_combination hP0
  have hQderiv : d Q = (5 / 2 : F) * d B + (9 / 4 : F) * L * d A := by
    linear_combination hQ0
  have hRderiv :
      d R = (5 / 2 : F) * d C0 + (9 / 4 : F) * L * d B +
        (2 : F) * A * d P + (2 : F) * P * d A -
        (25 / 4 : F) * A * d A := by
    linear_combination hR0
  have hSderiv :
      d S0 = (9 / 4 : F) * L * d C0 + (2 : F) * B * d P +
        (2 : F) * P * d B + (7 / 4 : F) * A * d Q +
        (7 / 4 : F) * Q * d A - (45 / 8 : F) * B * d A -
        (45 / 8 : F) * A * d B - (81 / 16 : F) * L * A * d A := by
    linear_combination hS0
  have hUderiv :
      d U0 = (7 / 4 : F) * Q * d C0 + (3 / 2 : F) * R * d B +
        (5 / 4 : F) * S0 * d A - (1 / 4 : F) * B * d R -
        (1 / 2 : F) * A * d S0 := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d U0 - (5 / 4 : F) * S0 * d A - (5 / 4 : F) * A * d S0 -
          (3 / 2 : F) * R * d B - (3 / 2 : F) * B * d R -
          (7 / 4 : F) * Q * d C0 - (7 / 4 : F) * C0 * d Q +
          (7 / 2 : F) * B * P * d A + (7 / 2 : F) * A * P * d B +
          (7 / 2 : F) * A * B * d P +
          (49 / 32 : F) * Q * ((2 : F) * A * d A) +
          (49 / 32 : F) * (A * A) * d Q +
          (63 / 16 : F) * L * C0 * d A + (63 / 16 : F) * L * A * d C0 +
          (63 / 32 : F) * L * ((2 : F) * B * d B) +
          (35 / 8 : F) * C0 * d B + (35 / 8 : F) * B * d C0 -
          (231 / 128 : F) * L * ((3 : F) * (A * A) * d A) -
          (385 / 64 : F) * B * ((2 : F) * A * d A) -
          (385 / 64 : F) * (A * A) * d B = 0 := by
    rw [hUderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    ring
  rw [hexp]
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h8, h16, h32,
    h52, h54, h32div, h74, h72, h4932, h6316, h6332, h358, h231128, h38564,
    hL, hsqA, hsqB, hcube, zero_mul, add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Seventh

/-! ## Affine depression of a degree-ten source, `z³` coefficient -/

section AffineDecic410Seventh

variable {k : Type*} [Field k] [CharZero k]

/-- The `z³` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff3_410
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 3 =
      -120 * r ^ 7 + 84 * (p.coeff 9 / h ^ 9) * r ^ 6 -
        56 * (p.coeff 8 / h ^ 8) * r ^ 5 +
        35 * (p.coeff 7 / h ^ 7) * r ^ 4 -
        20 * (p.coeff 6 / h ^ 6) * r ^ 3 +
        10 * (p.coeff 5 / h ^ 5) * r ^ 2 -
        4 * (p.coeff 4 / h ^ 4) * r + p.coeff 3 / h ^ 3 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6 - C (p.coeff 5) * X ^ 5 -
      C (p.coeff 4) * X ^ 4 - C (p.coeff 3) * X ^ 3
  have hplow : ∀ n, 3 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h3 | hlt3
    · subst n; simp
    · have : 4 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h4 | hlt4
      · subst n; simp
      · have : 5 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h5 | hlt5
        · subst n; simp
        · have : 6 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h6 | hlt6
          · subst n; simp
          · have : 7 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h7 | hlt7
            · subst n; simp
            · have : 8 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h8 | hlt8
              · subst n; simp
              · have : 9 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h9 | hlt9
                · subst n; simp
                · have : 10 ≤ n := by omega
                  rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                  · subst n; simp [hp10]
                  · simp [hp_high n (by omega), show n ≠ 10 by omega,
                      show n ≠ 9 by omega, show n ≠ 8 by omega,
                      show n ≠ 7 by omega, show n ≠ 6 by omega,
                      show n ≠ 5 by omega, show n ≠ 4 by omega,
                      show n ≠ 3 by omega]
  have hplowDeg : plow.natDegree ≤ 2 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + C (p.coeff 5) * X ^ 5 +
        C (p.coeff 4) * X ^ 4 + C (p.coeff 3) * X ^ 3 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H I J K s : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K).comp s =
          A.comp s + B.comp s + D.comp s + E.comp s + G.comp s +
            H.comp s + I.comp s + J.comp s + K.comp s := by
      have h1 : (A + B + D + E + G + H + I + J + K).comp s =
          (A + B + D + E + G + H + I + J).comp s + K.comp s := add_comp
      have h2 : (A + B + D + E + G + H + I + J).comp s =
          (A + B + D + E + G + H + I).comp s + J.comp s := add_comp
      have h3 : (A + B + D + E + G + H + I).comp s =
          (A + B + D + E + G + H).comp s + I.comp s := add_comp
      have h4 : (A + B + D + E + G + H).comp s =
          (A + B + D + E + G).comp s + H.comp s := add_comp
      have h5 : (A + B + D + E + G).comp s =
          (A + B + D + E).comp s + G.comp s := add_comp
      have h6 : (A + B + D + E).comp s =
          (A + B + D).comp s + E.comp s := add_comp
      have h7 : (A + B + D).comp s =
          (A + B).comp s + D.comp s := add_comp
      have h8 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 3 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 2 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 2 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 3 ≤ n))
  have h10_3 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -120 * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 3 hh]
    have hle : (3 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 3 = 120 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]; ring
  have h9_3 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 3 =
        84 * (p.coeff 9 / h ^ 9) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 3 hh]
    have hle : (3 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 3 = 84 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h8_3 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -56 * (p.coeff 8 / h ^ 8) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 3 hh]
    have hle : (3 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 3 = 56 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h7_3 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 3 =
        35 * (p.coeff 7 / h ^ 7) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 3 hh]
    have hle : (3 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 3 = 35 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h6_3 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -20 * (p.coeff 6 / h ^ 6) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 3 hh]
    have hle : (3 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 3 = 20 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]; ring
  have h5_3 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 3 =
        10 * (p.coeff 5 / h ^ 5) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 3 hh]
    have hle : (3 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 3 = 10 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]; ring
  have h4_3 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -4 * (p.coeff 4 / h ^ 4) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 3 hh]
    have hle : (3 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 3 = 4 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]; ring
  have h3_3 :
      ((C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹)).coeff 3 =
        p.coeff 3 / h ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 3 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add, coeff_add, h10_3, h9_3, h8_3, h7_3, h6_3, h5_3, h4_3, h3_3,
    hlow 3 (by omega)]
  ring

end AffineDecic410Seventh

/-! ## Local scalar identities at a simple root -/

section SeventhFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The sixth-face mixed relation specialises the second through fifth
defects to the one-parameter power jet in `t₁`. -/
theorem seventhFace_rootJet_410
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
    (hmix : t1 ^ 2 - (4 : F) * a2 = 0) :
    (2 : F) * s2 - (5 : F) * t1 ^ 2 = 0 ∧
      (4 : F) * v3 - (5 : F) * t1 ^ 3 = 0 ∧
      (16 : F) * w7 - (5 : F) * t1 ^ 4 = 0 ∧
      (32 : F) * b5 - t1 ^ 5 = 0 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have ha2 : (4 : F) * a2 = t1 ^ 2 := by linear_combination -hmix
  have hs : (8 : F) * s2 - (20 : F) * t1 ^ 2 = 0 := by
    linear_combination hM - (5 : F) * hmix
  have hs' : (2 : F) * s2 - (5 : F) * t1 ^ 2 = 0 := by
    linear_combination (1 / 4 : F) * hs
  have hT' : (64 : F) * v3 - (80 : F) * t1 ^ 3 = 0 := by
    linear_combination hT + (64 : F) * t1 * hs' + (20 : F) * t1 * hmix
  have hv' : (4 : F) * v3 - (5 : F) * t1 ^ 3 = 0 := by
    linear_combination (1 / 16 : F) * hT'
  have hUsub :
      (128 : F) * w7 - (224 : F) * t1 * v3 +
          (320 : F) * s2 * t1 ^ 2 - (525 : F) * t1 ^ 4 -
        (256 : F) * a2 * s2 + (400 : F) * a2 * t1 ^ 2 +
        (400 : F) * a2 ^ 2 =
        (128 : F) * w7 - (40 : F) * t1 ^ 4 := by
    have hs2 : s2 = (5 / 2 : F) * t1 ^ 2 := by
      have h2 : (2 : F) ≠ 0 := by norm_num
      field_simp [h2]
      linear_combination hs'
    have hv3 : v3 = (5 / 4 : F) * t1 ^ 3 := by
      field_simp [h4]
      linear_combination hv'
    have ha2' : a2 = t1 ^ 2 / 4 := by
      field_simp [h4]
      linear_combination ha2
    have h2 : (2 : F) ≠ 0 := by norm_num
    simp only [hs2, hv3, ha2']
    field_simp [h2, h4]
    ring
  have hU0 : (128 : F) * w7 - (40 : F) * t1 ^ 4 = 0 :=
    hUsub ▸ hU
  have hw' : (16 : F) * w7 - (5 : F) * t1 ^ 4 = 0 := by
    linear_combination (1 / 8 : F) * hU0
  have hVsub :
      (4096 : F) * b5 - (11520 : F) * a2 ^ 2 * t1 +
          (18432 : F) * a2 * s2 * t1 - (31200 : F) * a2 * t1 ^ 3 -
        (7168 : F) * a2 * v3 - (9984 : F) * s2 * t1 ^ 3 +
        (15912 : F) * t1 ^ 5 + (8064 : F) * t1 ^ 2 * v3 -
        (6144 : F) * t1 * w7 =
        (4096 : F) * b5 - (128 : F) * t1 ^ 5 := by
    have hs2 : s2 = (5 / 2 : F) * t1 ^ 2 := by
      have h2 : (2 : F) ≠ 0 := by norm_num
      field_simp [h2]
      linear_combination hs'
    have hv3 : v3 = (5 / 4 : F) * t1 ^ 3 := by
      field_simp [h4]
      linear_combination hv'
    have hw7 : w7 = (5 / 16 : F) * t1 ^ 4 := by
      have h16 : (16 : F) ≠ 0 := by norm_num
      field_simp [h16]
      linear_combination hw'
    have ha2' : a2 = t1 ^ 2 / 4 := by
      field_simp [h4]
      linear_combination ha2
    have h2 : (2 : F) ≠ 0 := by norm_num
    have h16 : (16 : F) ≠ 0 := by norm_num
    simp only [hs2, hv3, hw7, ha2']
    field_simp [h2, h4, h16]
    ring
  have hV0 : (4096 : F) * b5 - (128 : F) * t1 ^ 5 = 0 :=
    hVsub ▸ hV
  have hb' : (32 : F) * b5 - t1 ^ 5 = 0 := by
    linear_combination (1 / 128 : F) * hV0
  exact ⟨hs', hv', hw', hb'⟩

end SeventhFaceScalars410

/-! ## Source-facing seventh-face packet -/

section NonzeroSeventhFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The sixth quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²³`. -/
theorem nonzeroFace410_seventhDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedSeventhDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda =
        Polynomial.C eta * h0 ^ 23 := by
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
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
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
  have hg5 :
      g.coeff 5 =
        depressedS410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedS410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg3 :
      g.coeff 3 =
        depressedU410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedU410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
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
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
          (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
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
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 5)) = 0 :=
    deltaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 5) hLconst halpha0 hbeta0 (by simpa using hrow8)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst halpha0 hbeta0
      hgamma0 hdelta0 (by simpa using hrow6)
  obtain ⟨eta0, heta0⟩ :
      ∃ a : k,
        zetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 3) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hzeta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda) =
        (131072 : RatFunc k) * hRF ^ 23 *
          zetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 3) := by
    have hF := seventhDefect_eq_clearedZeta410 hRF a3 a2 a1 a0 b9 b8 b7
      b6 b5 b4 b3 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedSeventhDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b8,
      b7, b6, b5, b4, b3, zetaResidual410, alphaResidual410,
      betaResidual410, gammaResidual410, deltaResidual410, hf2, hf1, hf0,
      hg3, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (131072 * eta0) * h0 ^ 23) := by
    rw [hclear, heta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨131072 * eta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the sixth-face jet together with the
second through fifth defects forces the one-parameter identities
`2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`,
`16 (q₆/h²)(a) = 5 t₁⁴`, and `32 q₅(a) = t₁⁵`. -/
theorem nonzeroFace410_linearRoot_seventhInitialPacket
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
      h0 ^ 5 ∣ localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) ∧
      ∃ t1 s2 v3 w7 : k[X],
        p.coeff 3 = h0 ^ 2 * t1 ∧ q.coeff 8 = h0 ^ 6 * s2 ∧
          q.coeff 7 = h0 ^ 4 * v3 ∧ q.coeff 6 = h0 ^ 2 * w7 ∧
          (2 : k) * s2.eval a - (5 : k) * (t1.eval a) ^ 2 = 0 ∧
          (4 : k) * v3.eval a - (5 : k) * (t1.eval a) ^ 3 = 0 ∧
          (16 : k) * w7.eval a - (5 : k) * (t1.eval a) ^ 4 = 0 ∧
          (32 : k) * (q.coeff 5).eval a - (t1.eval a) ^ 5 = 0 := by
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
  obtain ⟨_eta, _hX⟩ :=
    nonzeroFace410_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨hp3pow, hq8pow, hq7pow, hq6pow, hq9pow, hmix5, hmix6⟩ :=
    nonzeroFace410_linearRoot_sixthInitialPacket p q H h0 j lambda a
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
  have hmixroot : (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a = 0 := by
    have hform :
        localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) =
          h0 ^ 4 * (t1 ^ 2 - (4 : k[X]) * p.coeff 2) := by
      simp only [localSixthMixed410, ht1]
      ring
    obtain ⟨rQ, hrQ⟩ := hmix6
    have hjet :
        t1 ^ 2 - (4 : k[X]) * p.coeff 2 = h0 * rQ := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
      calc
        h0 ^ 4 * (t1 ^ 2 - (4 : k[X]) * p.coeff 2) =
            localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) := hform.symm
        _ = h0 ^ 5 * rQ := hrQ
        _ = h0 ^ 4 * (h0 * rQ) := by ring
    have heval := congrArg (fun r : k[X] => r.eval a) hjet
    simpa [hroot, eval_pow] using heval
  obtain ⟨hsroot, hvroot, hwroot, hbroot⟩ :=
    seventhFace_rootJet_410 (t1.eval a) ((p.coeff 2).eval a)
      (s2.eval a) (v3.eval a) (w7.eval a) ((q.coeff 5).eval a)
      hMroot hTroot hUroot hVroot hmixroot
  exact ⟨⟨t1, ht1⟩, ⟨s2, hs2⟩, ⟨v3, hv3⟩, ⟨w7, hw7⟩, hq9pow, hmix5, hmix6,
    t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot, hbroot⟩

/-- Source-facing seventh integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_seventhDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSeventhDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda =
          Polynomial.C eta * h0 ^ 23 := by
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
  obtain ⟨eta, hX⟩ :=
    nonzeroFace410_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, eta, hh0, hlambda, hh0degree, hH, hN', hX⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the sixth-face jet together with the one-parameter
identities `2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`,
`16 (q₆/h²)(a) = 5 t₁⁴`, and `32 q₅(a) = t₁⁵`. -/
theorem normalized410ScaleTwo_nonzeroFace_seventhInitialPacket
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
        (∃ t1 s2 v3 w7 : K[X],
          p.coeff 3 = h0 ^ 2 * t1 ∧ q.coeff 8 = h0 ^ 6 * s2 ∧
            q.coeff 7 = h0 ^ 4 * v3 ∧ q.coeff 6 = h0 ^ 2 * w7 ∧
            (2 : K) * s2.eval a - (5 : K) * (t1.eval a) ^ 2 = 0 ∧
            (4 : K) * v3.eval a - (5 : K) * (t1.eval a) ^ 3 = 0 ∧
            (16 : K) * w7.eval a - (5 : K) * (t1.eval a) ^ 4 = 0 ∧
            (32 : K) * (q.coeff 5).eval a - (t1.eval a) ^ 5 = 0) ∧
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
  obtain ⟨hp3, hq8, hq7, hq6, hq9, hmix5, hmix6, hjet⟩ :=
    nonzeroFace410_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq6, hq9, hmix5, hmix6, hjet, hN'⟩

end NonzeroSeventhFace410

#print axioms seventhCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_6_monicQuarticDecic
#print axioms seventhDefect_eq_clearedZeta410
#print axioms seventhFace_rootJet_410
#print axioms nonzeroFace410_seventhDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_seventhInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_seventhDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_seventhInitialPacket

end Max11DegreeRoutes
