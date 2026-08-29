import LowScale410ScaleTwoSeventhFace

/-! # Scale-two eighth face for normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the seventh face supplies the degree-`6` integral and
the one-parameter jet `h² ∣ p₃`, `h⁶ ∣ q₈`, `h⁴ ∣ q₇`, `h² ∣ q₆`,
`h⁸ ∣ q₉` together with `h¹¹ ∣ 3 p₃⁵ - 40 p₂ p₃³ h⁴ + 240 p₂² p₃ h⁸
- 256 q₅ h¹⁰`, `h⁵ ∣ p₃² - 4 p₂ h⁴`, and the root identities
`2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`, `16 (q₆/h²)(a) = 5 t₁⁴`,
and `32 q₅(a) = t₁⁵` on `p₃ = t₁ h²` and `4 p₂(a) = t₁²`.  The next
Keller coefficient is the degree-`5` Jacobian row.  After the same
quartic depression that kills `z³`, that row is
`6 R C' + 5 S B' + 4 T A' - B S' - 2 A T' - 4 V' = 0`.  The resulting
first integral clears to a polynomial defect `Y` of weight twenty-six.

Evaluating that defect on the seventh-face jet at the root of `h` is
compatible with the one-parameter identities and does not force
`t₁(a) = 0`.  No further individual vanishing of `p₁, p₀, q₄, q₃, q₂`
is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eighth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  It is the source of the first mixed quartic/decic
`z⁰`/`z²` defect after the degree-`6` integral. -/
theorem eighthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-! ## Quartic constant and decic `z²` coordinates -/

section Depression410Eighth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z²` coefficient. -/
def depressedV410 (h r b9 b8 b7 b6 b5 b4 b3 b2 : F) : F :=
  45 * r ^ 8 - 36 * (b9 / h ^ 9) * r ^ 7 +
    28 * (b8 / h ^ 8) * r ^ 6 - 21 * (b7 / h ^ 7) * r ^ 5 +
    15 * (b6 / h ^ 6) * r ^ 4 - 10 * (b5 / h ^ 5) * r ^ 3 +
    6 * (b4 / h ^ 4) * r ^ 2 - 3 * (b3 / h ^ 3) * r + b2 / h ^ 2

/-- First residual of the degree-`5` row.  Equivalent to
`V + (5/128) A⁴ - (45/128) L A² B - (15/16) A² C - (3/8) γ A²
- (15/16) A B² - (21/16) β A B - 2 α A C - α B² - (45/16) L B C
- ε A - (5/4) δ B - (15/8) C² - (3/2) γ C`
on the second- through sixth-face integrals. -/
def etaResidual410 (L A B C0 P Q R S0 T0 V0 : F) : F :=
  V0 + (5 / 128 : F) * A ^ 4 -
    (45 / 128 : F) * L * A ^ 2 * B -
    (15 / 16 : F) * A ^ 2 * C0 -
    (3 / 8 : F) * gammaResidual410 L A B C0 P R * A ^ 2 -
    (15 / 16 : F) * A * B ^ 2 -
    (21 / 16 : F) * betaResidual410 L A B Q * A * B -
    (2 : F) * alphaResidual410 A P * A * C0 -
    alphaResidual410 A P * B ^ 2 -
    (45 / 16 : F) * L * B * C0 -
    epsilonResidual410 L A B C0 P Q R T0 * A -
    (5 / 4 : F) * deltaResidual410 L A B C0 P Q S0 * B -
    (15 / 8 : F) * C0 ^ 2 -
    (3 / 2 : F) * gammaResidual410 L A B C0 P R * C0

/-- Polynomial numerator of `32768 h²⁶ η` on the ninth-power face. -/
def localClearedEighthDefect410
    (h a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : F[X]) (lambda : F) : F[X] :=
  (29568 : F[X]) * a3 ^ 6 * b8 -
    (45045 : F[X]) * a3 ^ 8 * h ^ 2 -
    (161280 : F[X]) * a2 * a3 ^ 4 * b8 * h ^ 4 -
    (28224 : F[X]) * a3 ^ 5 * b7 * h ^ 4 +
    (15444 : F[X]) * Polynomial.C lambda * a3 ^ 7 * h ^ 5 +
    (258720 : F[X]) * a2 * a3 ^ 6 * h ^ 6 +
    (143360 : F[X]) * a1 * a3 ^ 3 * b8 * h ^ 8 +
    (215040 : F[X]) * a2 ^ 2 * a3 ^ 2 * b8 * h ^ 8 +
    (125440 : F[X]) * a2 * a3 ^ 3 * b7 * h ^ 8 +
    (26880 : F[X]) * a3 ^ 4 * b6 * h ^ 8 -
    (99792 : F[X]) * Polynomial.C lambda * a2 * a3 ^ 5 * h ^ 9 -
    (231840 : F[X]) * a1 * a3 ^ 5 * h ^ 10 -
    (352800 : F[X]) * a2 ^ 2 * a3 ^ 4 * h ^ 10 -
    (122880 : F[X]) * a0 * a3 ^ 2 * b8 * h ^ 12 -
    (245760 : F[X]) * a1 * a2 * a3 * b8 * h ^ 12 -
    (107520 : F[X]) * a1 * a3 ^ 2 * b7 * h ^ 12 -
    (107520 : F[X]) * a2 ^ 2 * a3 * b7 * h ^ 12 -
    (40960 : F[X]) * a2 ^ 3 * b8 * h ^ 12 -
    (92160 : F[X]) * a2 * a3 ^ 2 * b6 * h ^ 12 -
    (25600 : F[X]) * a3 ^ 3 * b5 * h ^ 12 +
    (90720 : F[X]) * Polynomial.C lambda * a1 * a3 ^ 4 * h ^ 13 +
    (181440 : F[X]) * Polynomial.C lambda * a2 ^ 2 * a3 ^ 3 * h ^ 13 +
    (201600 : F[X]) * a0 * a3 ^ 4 * h ^ 14 +
    (403200 : F[X]) * a1 * a2 * a3 ^ 3 * h ^ 14 +
    (98304 : F[X]) * a0 * a2 * b8 * h ^ 16 +
    (86016 : F[X]) * a0 * a3 * b7 * h ^ 16 +
    (49152 : F[X]) * a1 ^ 2 * b8 * h ^ 16 +
    (86016 : F[X]) * a1 * a2 * b7 * h ^ 16 +
    (73728 : F[X]) * a1 * a3 * b6 * h ^ 16 +
    (36864 : F[X]) * a2 ^ 2 * b6 * h ^ 16 +
    (61440 : F[X]) * a2 * a3 * b5 * h ^ 16 +
    (24576 : F[X]) * a3 ^ 2 * b4 * h ^ 16 -
    (80640 : F[X]) * Polynomial.C lambda * a0 * a3 ^ 3 * h ^ 17 -
    (241920 : F[X]) * Polynomial.C lambda * a1 * a2 * a3 ^ 2 * h ^ 17 -
    (80640 : F[X]) * Polynomial.C lambda * a2 ^ 3 * a3 * h ^ 17 -
    (153600 : F[X]) * a0 * a2 * a3 ^ 2 * h ^ 18 -
    (76800 : F[X]) * a1 ^ 2 * a3 ^ 2 * h ^ 18 +
    (192000 : F[X]) * a1 * a2 ^ 2 * a3 * h ^ 18 +
    (44800 : F[X]) * a2 ^ 4 * h ^ 18 -
    (49152 : F[X]) * a0 * b6 * h ^ 20 -
    (40960 : F[X]) * a1 * b5 * h ^ 20 -
    (32768 : F[X]) * a2 * b4 * h ^ 20 -
    (24576 : F[X]) * a3 * b3 * h ^ 20 +
    (138240 : F[X]) * Polynomial.C lambda * a0 * a2 * a3 * h ^ 21 +
    (69120 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a3 * h ^ 21 +
    (69120 : F[X]) * Polynomial.C lambda * a1 * a2 ^ 2 * h ^ 21 -
    (30720 : F[X]) * a0 * a1 * a3 * h ^ 22 -
    (153600 : F[X]) * a0 * a2 ^ 2 * h ^ 22 -
    (153600 : F[X]) * a1 ^ 2 * a2 * h ^ 22 +
    (32768 : F[X]) * b2 * h ^ 24 -
    (55296 : F[X]) * Polynomial.C lambda * a0 * a1 * h ^ 25 +
    (61440 : F[X]) * a0 ^ 2 * h ^ 26

/-- Exact denominator clearing for the decic `z²` coordinate on the
ninth-power face. -/
theorem depressedV410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedV410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 b3
        b2 =
      (-315 * a3 ^ 8 * h ^ 2 + 72 * lambda * a3 ^ 7 * h ^ 5 +
          448 * a3 ^ 6 * b8 - 1344 * a3 ^ 5 * b7 * h ^ 4 +
          3840 * a3 ^ 4 * b6 * h ^ 8 - 10240 * a3 ^ 3 * b5 * h ^ 12 +
          24576 * a3 ^ 2 * b4 * h ^ 16 - 49152 * a3 * b3 * h ^ 20 +
          65536 * b2 * h ^ 24) /
        (65536 * h ^ 26) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh26 : h ^ 26 ≠ 0 := pow_ne_zero 26 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedV410, quarticDepressionR410, quarticDepressionR46]
  have hrewrite :
      45 * (a3 / (4 * h ^ 3)) ^ 8 -
          36 * (b9 / h ^ 9) * (a3 / (4 * h ^ 3)) ^ 7 +
        28 * (b8 / h ^ 8) * (a3 / (4 * h ^ 3)) ^ 6 -
          21 * (b7 / h ^ 7) * (a3 / (4 * h ^ 3)) ^ 5 +
        15 * (b6 / h ^ 6) * (a3 / (4 * h ^ 3)) ^ 4 -
          10 * (b5 / h ^ 5) * (a3 / (4 * h ^ 3)) ^ 3 +
        6 * (b4 / h ^ 4) * (a3 / (4 * h ^ 3)) ^ 2 -
          3 * (b3 / h ^ 3) * (a3 / (4 * h ^ 3)) + b2 / h ^ 2 =
        (-315 * a3 ^ 8 * h ^ 2 + 72 * lambda * a3 ^ 7 * h ^ 5 +
            448 * a3 ^ 6 * b8 - 1344 * a3 ^ 5 * b7 * h ^ 4 +
            3840 * a3 ^ 4 * b6 * h ^ 8 - 10240 * a3 ^ 3 * b5 * h ^ 12 +
            24576 * a3 ^ 2 * b4 * h ^ 16 - 49152 * a3 * b3 * h ^ 20 +
            65536 * b2 * h ^ 24) /
          (65536 * h ^ 26) := by
    field_simp [hh, h2, h4, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh26, h65536]
    have hb9' :
        b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 := by
      field_simp [h2]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h2, h4, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh26, h65536]
    ring
  exact hrewrite

set_option maxHeartbeats 24000000 in
/-- Clearing the first integral
`V + (5/128) A⁴ - (45/128) L A² B - (15/16) A² C - (3/8) γ A²
- (15/16) A B² - (21/16) β A B - 2 α A C - α B² - (45/16) L B C
- ε A - (5/4) δ B - (15/8) C² - (3/2) γ C`
against `h²⁶` on the ninth-power face. -/
theorem eighthDefect_eq_clearedEta410
    (h a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (32768 : F) * h ^ 26 *
        etaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6)
          (depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5)
          (depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 b4)
          (depressedV410 h (quarticDepressionR410 h a3) b9 b8 b7 b6
            b5 b4 b3 b2) =
      (29568 : F) * a3 ^ 6 * b8 -
        (45045 : F) * a3 ^ 8 * h ^ 2 -
        (161280 : F) * a2 * a3 ^ 4 * b8 * h ^ 4 -
        (28224 : F) * a3 ^ 5 * b7 * h ^ 4 +
        (15444 : F) * lambda * a3 ^ 7 * h ^ 5 +
        (258720 : F) * a2 * a3 ^ 6 * h ^ 6 +
        (143360 : F) * a1 * a3 ^ 3 * b8 * h ^ 8 +
        (215040 : F) * a2 ^ 2 * a3 ^ 2 * b8 * h ^ 8 +
        (125440 : F) * a2 * a3 ^ 3 * b7 * h ^ 8 +
        (26880 : F) * a3 ^ 4 * b6 * h ^ 8 -
        (99792 : F) * lambda * a2 * a3 ^ 5 * h ^ 9 -
        (231840 : F) * a1 * a3 ^ 5 * h ^ 10 -
        (352800 : F) * a2 ^ 2 * a3 ^ 4 * h ^ 10 -
        (122880 : F) * a0 * a3 ^ 2 * b8 * h ^ 12 -
        (245760 : F) * a1 * a2 * a3 * b8 * h ^ 12 -
        (107520 : F) * a1 * a3 ^ 2 * b7 * h ^ 12 -
        (107520 : F) * a2 ^ 2 * a3 * b7 * h ^ 12 -
        (40960 : F) * a2 ^ 3 * b8 * h ^ 12 -
        (92160 : F) * a2 * a3 ^ 2 * b6 * h ^ 12 -
        (25600 : F) * a3 ^ 3 * b5 * h ^ 12 +
        (90720 : F) * lambda * a1 * a3 ^ 4 * h ^ 13 +
        (181440 : F) * lambda * a2 ^ 2 * a3 ^ 3 * h ^ 13 +
        (201600 : F) * a0 * a3 ^ 4 * h ^ 14 +
        (403200 : F) * a1 * a2 * a3 ^ 3 * h ^ 14 +
        (98304 : F) * a0 * a2 * b8 * h ^ 16 +
        (86016 : F) * a0 * a3 * b7 * h ^ 16 +
        (49152 : F) * a1 ^ 2 * b8 * h ^ 16 +
        (86016 : F) * a1 * a2 * b7 * h ^ 16 +
        (73728 : F) * a1 * a3 * b6 * h ^ 16 +
        (36864 : F) * a2 ^ 2 * b6 * h ^ 16 +
        (61440 : F) * a2 * a3 * b5 * h ^ 16 +
        (24576 : F) * a3 ^ 2 * b4 * h ^ 16 -
        (80640 : F) * lambda * a0 * a3 ^ 3 * h ^ 17 -
        (241920 : F) * lambda * a1 * a2 * a3 ^ 2 * h ^ 17 -
        (80640 : F) * lambda * a2 ^ 3 * a3 * h ^ 17 -
        (153600 : F) * a0 * a2 * a3 ^ 2 * h ^ 18 -
        (76800 : F) * a1 ^ 2 * a3 ^ 2 * h ^ 18 +
        (192000 : F) * a1 * a2 ^ 2 * a3 * h ^ 18 +
        (44800 : F) * a2 ^ 4 * h ^ 18 -
        (49152 : F) * a0 * b6 * h ^ 20 -
        (40960 : F) * a1 * b5 * h ^ 20 -
        (32768 : F) * a2 * b4 * h ^ 20 -
        (24576 : F) * a3 * b3 * h ^ 20 +
        (138240 : F) * lambda * a0 * a2 * a3 * h ^ 21 +
        (69120 : F) * lambda * a1 ^ 2 * a3 * h ^ 21 +
        (69120 : F) * lambda * a1 * a2 ^ 2 * h ^ 21 -
        (30720 : F) * a0 * a1 * a3 * h ^ 22 -
        (153600 : F) * a0 * a2 ^ 2 * h ^ 22 -
        (153600 : F) * a1 ^ 2 * a2 * h ^ 22 +
        (32768 : F) * b2 * h ^ 24 -
        (55296 : F) * lambda * a0 * a1 * h ^ 25 +
        (61440 : F) * a0 ^ 2 * h ^ 26 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh11 : h ^ 11 ≠ 0 := pow_ne_zero 11 hh
  have hh12 : h ^ 12 ≠ 0 := pow_ne_zero 12 hh
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh17 : h ^ 17 ≠ 0 := pow_ne_zero 17 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh23 : h ^ 23 ≠ 0 := pow_ne_zero 23 hh
  have hh26 : h ^ 26 ≠ 0 := pow_ne_zero 26 hh
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
  have hT :
      depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
          b4 =
        (-525 * a3 ^ 6 * h ^ 2 + 126 * lambda * a3 ^ 5 * h ^ 5 +
            560 * a3 ^ 4 * b8 - 1120 * a3 ^ 3 * b7 * h ^ 4 +
            1920 * a3 ^ 2 * b6 * h ^ 8 - 2560 * a3 * b5 * h ^ 12 +
            2048 * b4 * h ^ 16) / (2048 * h ^ 20) :=
    depressedT410_eq_cleared h a3 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hV :
      depressedV410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
          b4 b3 b2 =
        (-315 * a3 ^ 8 * h ^ 2 + 72 * lambda * a3 ^ 7 * h ^ 5 +
            448 * a3 ^ 6 * b8 - 1344 * a3 ^ 5 * b7 * h ^ 4 +
            3840 * a3 ^ 4 * b6 * h ^ 8 - 10240 * a3 ^ 3 * b5 * h ^ 12 +
            24576 * a3 ^ 2 * b4 * h ^ 16 - 49152 * a3 * b3 * h ^ 20 +
            65536 * b2 * h ^ 24) / (65536 * h ^ 26) :=
    depressedV410_eq_cleared h a3 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  simp only [etaResidual410, hL, hA, hB, hC, hP, hQ, hR, hS, hT, hV,
    alphaResidual410, betaResidual410, gammaResidual410,
    deltaResidual410, epsilonResidual410]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h256, h2048, h32768,
    h65536, hh6, hh8pow, hh9, hh11, hh12, hh14, hh17, hh20, hh23, hh26]
  ring

end Depression410Eighth

/-! ## Degree-`5` depressed Jacobian coefficient -/

section DepressedRow410Eighth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`5` Jacobian coefficient is
exactly `6 R C' + 5 S B' + 4 T A' - B S' - 2 A T' - 4 V'`. -/
theorem differentialJacobian_coeff_5_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (4 : F) * d (g.coeff 2) := by
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
  have hmem05 : ((0, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem14 : ((1, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem23 : ((2, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem32 : ((3, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 5 =
        (6 : F) * g.coeff 6 * d (f.coeff 0) +
          (5 : F) * g.coeff 5 * d (f.coeff 1) +
          (4 : F) * g.coeff 4 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne01 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne02 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne12 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hsubset : ({(0, 5), (1, 4), (2, 3)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem05
      · subst b; exact hmem14
      · subst b; exact hmem23
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (2, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne05 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne14 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne23 : b ≠ (2, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 3 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne05
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne14
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne23
          ext
          · exact h2
          · omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 3 := by
      rw [Finset.sum_insert (by simp [hne01, hne02]),
        Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder5, hder4, hder3]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 5 =
        f.coeff 1 * d (g.coeff 5) +
          (2 : F) * f.coeff 2 * d (g.coeff 4) +
          (4 : F) * d (g.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne05_14 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne05_32 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne14_32 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hsubset : ({(0, 5), (1, 4), (3, 2)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem05
      · subst b; exact hmem14
      · subst b; exact hmem32
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (3, 2)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne05 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne14 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne32 : b ≠ (3, 2) := by
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
            apply hne05
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne14
            ext
            · exact h1
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne32
            ext
            · exact h3
            · omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 5), (1, 4), (3, 2)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 2 := by
      rw [Finset.sum_insert (by simp [hne05_14, hne05_32]),
        Finset.sum_insert (by simp [hne14_32]), Finset.sum_singleton]
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

set_option maxHeartbeats 8000000 in
theorem etaResidual410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q R S0 T0 V0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hgamma : d (gammaResidual410 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual410 L A B C0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual410 L A B C0 P Q R T0) = 0)
    (hrow : (6 : F) * R * d C0 + (5 : F) * S0 * d B +
        (4 : F) * T0 * d A - B * d S0 - (2 : F) * A * d T0 -
        (4 : F) * d V0 = 0) :
    d (etaResidual410 L A B C0 P Q R S0 T0 V0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h21 : d (21 : F) = 0 := d.map_natCast 21
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h135 : d (135 : F) = 0 := d.map_natCast 135
  have h175 : d (175 : F) = 0 := d.map_natCast 175
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
  have h92 : d (9 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h9]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h15]
  have h218 : d (21 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h21]
  have h278 : d (27 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h27]
  have h1516 : d (15 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h15]
  have h2116 : d (21 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h21]
  have h4516 : d (45 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h45]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h7516 : d (75 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h75]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have h13532 : d (135 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h135]
  have h175128 : d (175 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h175]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h45128 : d (45 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h45]
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
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]; ring
  have hcube : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hfourth : d (A * A * A * A) = (4 : F) * (A * A * A) * d A := by
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
  have hT0 :
      d T0 - (2 : F) * C0 * d P - (2 : F) * P * d C0 -
          (7 / 4 : F) * B * d Q - (7 / 4 : F) * Q * d B -
          (3 / 2 : F) * A * d R - (3 / 2 : F) * R * d A +
          (2 : F) * (A * A) * d P + (4 : F) * P * A * d A +
          (9 / 2 : F) * L * B * d A + (9 / 2 : F) * L * A * d B +
          (5 : F) * C0 * d A + (5 : F) * A * d C0 +
          (5 : F) * B * d B - (15 / 2 : F) * (A * A) * d A = 0 := by
    have hexp :
        epsilonResidual410 L A B C0 P Q R T0 =
          T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A) := by
      simp only [epsilonResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, pow_two, pow_three]
      ring
    have hdg :
        d (T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A)) = 0 := by
      simpa [hexp] using hepsilon
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h5, h52, h74,
      h32div, h92, hL, hsqA, hsqB, hcube, zero_mul, add_zero,
      mul_zero] at hdg
    linear_combination hdg
  have hexp :
      etaResidual410 L A B C0 P Q R S0 T0 V0 =
        V0 - A * T0 - (5 / 4 : F) * B * S0 +
          (9 / 8 : F) * (A * A) * R - (3 / 2 : F) * C0 * R +
          (21 / 8 : F) * A * B * Q + (3 : F) * A * C0 * P +
          (3 / 2 : F) * (B * B) * P + (27 / 8 : F) * L * B * C0 -
          (5 / 4 : F) * (A * A * A) * P +
          (175 / 128 : F) * (A * A * A * A) -
          (135 / 32 : F) * L * (A * A) * B -
          (75 / 16 : F) * (A * A) * C0 -
          (75 / 16 : F) * A * (B * B) + (15 / 8 : F) * (C0 * C0) := by
    simp only [etaResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, deltaResidual410, epsilonResidual410, pow_two,
      pow_three]
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
  have hTderiv :
      d T0 = (2 : F) * C0 * d P + (2 : F) * P * d C0 +
        (7 / 4 : F) * B * d Q + (7 / 4 : F) * Q * d B +
        (3 / 2 : F) * A * d R + (3 / 2 : F) * R * d A -
        (2 : F) * (A * A) * d P - (4 : F) * P * A * d A -
        (9 / 2 : F) * L * B * d A - (9 / 2 : F) * L * A * d B -
        (5 : F) * C0 * d A - (5 : F) * A * d C0 -
        (5 : F) * B * d B + (15 / 2 : F) * (A * A) * d A := by
    linear_combination hT0
  have hVderiv :
      d V0 = (3 / 2 : F) * R * d C0 + (5 / 4 : F) * S0 * d B +
        T0 * d A - (1 / 4 : F) * B * d S0 - (1 / 2 : F) * A * d T0 := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d V0 - T0 * d A - A * d T0 - (5 / 4 : F) * S0 * d B -
          (5 / 4 : F) * B * d S0 + (9 / 8 : F) * R * ((2 : F) * A * d A) +
          (9 / 8 : F) * (A * A) * d R - (3 / 2 : F) * R * d C0 -
          (3 / 2 : F) * C0 * d R + (21 / 8 : F) * B * Q * d A +
          (21 / 8 : F) * A * Q * d B + (21 / 8 : F) * A * B * d Q +
          (3 : F) * C0 * P * d A + (3 : F) * A * P * d C0 +
          (3 : F) * A * C0 * d P +
          (3 / 2 : F) * P * ((2 : F) * B * d B) +
          (3 / 2 : F) * (B * B) * d P + (27 / 8 : F) * L * C0 * d B +
          (27 / 8 : F) * L * B * d C0 -
          (5 / 4 : F) * P * ((3 : F) * (A * A) * d A) -
          (5 / 4 : F) * (A * A * A) * d P +
          (175 / 128 : F) * ((4 : F) * (A * A * A) * d A) -
          (135 / 32 : F) * L * B * ((2 : F) * A * d A) -
          (135 / 32 : F) * L * (A * A) * d B -
          (75 / 16 : F) * C0 * ((2 : F) * A * d A) -
          (75 / 16 : F) * (A * A) * d C0 -
          (75 / 16 : F) * (B * B) * d A -
          (75 / 16 : F) * A * ((2 : F) * B * d B) +
          (15 / 8 : F) * ((2 : F) * C0 * d C0) = 0 := by
    rw [hVderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    ring
  rw [hexp]
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h8, h16,
    h32, h128, h52, h54, h32div, h74, h92, h98, h38, h158, h218, h278,
    h1516, h2116, h4516, h516, h7516, h13532, h175128, h5128, h45128, hL,
    hsqA, hsqB, hsqC, hcube, hfourth, zero_mul, add_zero, mul_zero]
  linear_combination htarget

end DepressedRow410Eighth

/-! ## Affine depression of a degree-ten source, `z²` coefficient -/

section AffineDecic410Eighth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z²` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff2_410
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 2 =
      45 * r ^ 8 - 36 * (p.coeff 9 / h ^ 9) * r ^ 7 +
        28 * (p.coeff 8 / h ^ 8) * r ^ 6 -
        21 * (p.coeff 7 / h ^ 7) * r ^ 5 +
        15 * (p.coeff 6 / h ^ 6) * r ^ 4 -
        10 * (p.coeff 5 / h ^ 5) * r ^ 3 +
        6 * (p.coeff 4 / h ^ 4) * r ^ 2 -
        3 * (p.coeff 3 / h ^ 3) * r + p.coeff 2 / h ^ 2 := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6 - C (p.coeff 5) * X ^ 5 -
      C (p.coeff 4) * X ^ 4 - C (p.coeff 3) * X ^ 3 -
      C (p.coeff 2) * X ^ 2
  have hplow : ∀ n, 2 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h2 | hlt2
    · subst n; simp
    · have : 3 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h3 | hlt3
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
                        show n ≠ 3 by omega, show n ≠ 2 by omega]
  have hplowDeg : plow.natDegree ≤ 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + C (p.coeff 5) * X ^ 5 +
        C (p.coeff 4) * X ^ 4 + C (p.coeff 3) * X ^ 3 +
        C (p.coeff 2) * X ^ 2 + plow := by
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
          (C (p.coeff 2) * X ^ 2).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H I J K s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + s).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + s.comp t :=
        add_comp
      have h2 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t := add_comp
      have h3 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t := add_comp
      have h4 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t := add_comp
      have h5 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := add_comp
      have h6 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := add_comp
      have h7 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := add_comp
      have h8 : (A + B + D).comp t = (A + B).comp t + D.comp t := add_comp
      have h9 : (A + B).comp t = A.comp t + B.comp t := add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 2 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 1 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 1 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 2 ≤ n))
  have h10_2 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 2 =
        45 * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 2 hh]
    have hle : (2 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 2 = 45 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]; ring
  have h9_2 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 2 =
        -36 * (p.coeff 9 / h ^ 9) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 2 hh]
    have hle : (2 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 2 = 36 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h8_2 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 2 =
        28 * (p.coeff 8 / h ^ 8) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 2 hh]
    have hle : (2 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 2 = 28 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h7_2 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 2 =
        -21 * (p.coeff 7 / h ^ 7) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 2 hh]
    have hle : (2 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 2 = 21 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h6_2 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 2 =
        15 * (p.coeff 6 / h ^ 6) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 2 hh]
    have hle : (2 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 2 = 15 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h5_2 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 2 =
        -10 * (p.coeff 5 / h ^ 5) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 2 hh]
    have hle : (2 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 2 = 10 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]; ring
  have h4_2 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 2 =
        6 * (p.coeff 4 / h ^ 4) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 2 hh]
    have hle : (2 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 2 = 6 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]; ring
  have h3_2 :
      ((C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹)).coeff 2 =
        -3 * (p.coeff 3 / h ^ 3) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 2 hh]
    have hle : (2 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 2 = 3 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]; ring
  have h2_2 :
      ((C (p.coeff 2) * X ^ 2).comp ((X - C r) * C h⁻¹)).coeff 2 =
        p.coeff 2 / h ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 2 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add, coeff_add, coeff_add, h10_2, h9_2, h8_2, h7_2, h6_2, h5_2,
    h4_2, h3_2, h2_2, hlow 2 (by omega)]
  ring

end AffineDecic410Eighth

/-! ## Seventh-jet compatibility at a simple root -/

section EighthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The eighth defect's leading form at the root of `h` vanishes on the
seventh-face one-parameter jet and does not force `t₁ = 0`. -/
theorem eighthFace_rootCompatible_410
    (t1 a2 s2 v3 w7 b5 : F)
    (hs : (2 : F) * s2 - (5 : F) * t1 ^ 2 = 0)
    (hv : (4 : F) * v3 - (5 : F) * t1 ^ 3 = 0)
    (hw : (16 : F) * w7 - (5 : F) * t1 ^ 4 = 0)
    (hb : (32 : F) * b5 - t1 ^ 5 = 0)
    (hmix : t1 ^ 2 - (4 : F) * a2 = 0) :
    (44800 : F) * a2 ^ 4 - (40960 : F) * a2 ^ 3 * s2 +
        (215040 : F) * a2 ^ 2 * s2 * t1 ^ 2 -
        (352800 : F) * a2 ^ 2 * t1 ^ 4 -
        (107520 : F) * a2 ^ 2 * t1 * v3 +
        (36864 : F) * a2 ^ 2 * w7 + (61440 : F) * a2 * b5 * t1 -
        (161280 : F) * a2 * s2 * t1 ^ 4 + (258720 : F) * a2 * t1 ^ 6 +
        (125440 : F) * a2 * t1 ^ 3 * v3 -
        (92160 : F) * a2 * t1 ^ 2 * w7 - (25600 : F) * b5 * t1 ^ 3 +
        (29568 : F) * s2 * t1 ^ 6 - (45045 : F) * t1 ^ 8 -
        (28224 : F) * t1 ^ 5 * v3 + (26880 : F) * t1 ^ 4 * w7 =
      0 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have hs2 : s2 = (5 / 2 : F) * t1 ^ 2 := by
    field_simp [h2]
    linear_combination hs
  have hv3 : v3 = (5 / 4 : F) * t1 ^ 3 := by
    field_simp [h4]
    linear_combination hv
  have hw7 : w7 = (5 / 16 : F) * t1 ^ 4 := by
    field_simp [h16]
    linear_combination hw
  have hb5 : b5 = t1 ^ 5 / 32 := by
    field_simp [h32]
    linear_combination hb
  have ha2 : a2 = t1 ^ 2 / 4 := by
    field_simp [h4]
    linear_combination -hmix
  simp only [hs2, hv3, hw7, hb5, ha2]
  field_simp [h2, h4, h16, h32]
  ring

end EighthFaceScalars410

/-! ## Source-facing eighth-face packet -/

section NonzeroEighthFace410

variable {k : Type*} [Field k] [CharZero k]

/-- The seventh quartic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h²⁶`. -/
theorem nonzeroFace410_eighthDefectPowerRelation
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
      localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda =
        Polynomial.C eta * h0 ^ 26 := by
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
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
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
  have hg4 :
      g.coeff 4 =
        depressedT410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedT410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedV410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
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
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
          (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
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
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4)) = 0 :=
    epsilonResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 4) hLconst halpha0 hbeta0 hgamma0
      (by simpa using hrow7)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0
      hbeta0 hgamma0 hdelta0 hepsilon0 (by simpa using hrow5)
  obtain ⟨eta0, heta0⟩ :
      ∃ a : k,
        etaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 2) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      heta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) lambda) =
        (32768 : RatFunc k) * hRF ^ 26 *
          etaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 2) := by
    have hF := eighthDefect_eq_clearedEta410 hRF a3 a2 a1 a0 b9 b8 b7
      b6 b5 b4 b3 b2 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedEighthDefect410, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b8,
      b7, b6, b5, b4, b3, b2, etaResidual410, alphaResidual410,
      betaResidual410, gammaResidual410, deltaResidual410,
      epsilonResidual410, hf2, hf1, hf0, hg2, hg4, hg5, hg6, hg7, hg8',
      hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (32768 * eta0) * h0 ^ 26) := by
    rw [hclear, heta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨32768 * eta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the seventh-face jet together with the
eighth integral.  The degree-`5` defect is compatible with
`2 (q₈/h⁶)(a) = 5 t₁²`, `4 (q₇/h⁴)(a) = 5 t₁³`,
`16 (q₆/h²)(a) = 5 t₁⁴`, and `32 q₅(a) = t₁⁵` and does not force
`t₁(a) = 0`. -/
theorem nonzeroFace410_linearRoot_eighthInitialPacket
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
      (∃ eta : k,
        localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) lambda =
          Polynomial.C eta * h0 ^ 26) ∧
      ∃ t1 s2 v3 w7 : k[X],
        p.coeff 3 = h0 ^ 2 * t1 ∧ q.coeff 8 = h0 ^ 6 * s2 ∧
          q.coeff 7 = h0 ^ 4 * v3 ∧ q.coeff 6 = h0 ^ 2 * w7 ∧
          (2 : k) * s2.eval a - (5 : k) * (t1.eval a) ^ 2 = 0 ∧
          (4 : k) * v3.eval a - (5 : k) * (t1.eval a) ^ 3 = 0 ∧
          (16 : k) * w7.eval a - (5 : k) * (t1.eval a) ^ 4 = 0 ∧
          (32 : k) * (q.coeff 5).eval a - (t1.eval a) ^ 5 = 0 ∧
          (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a = 0 ∧
          (44800 : k) * ((p.coeff 2).eval a) ^ 4 -
              (40960 : k) * ((p.coeff 2).eval a) ^ 3 * s2.eval a +
            (215040 : k) * ((p.coeff 2).eval a) ^ 2 * s2.eval a *
                (t1.eval a) ^ 2 -
              (352800 : k) * ((p.coeff 2).eval a) ^ 2 *
                (t1.eval a) ^ 4 -
            (107520 : k) * ((p.coeff 2).eval a) ^ 2 * t1.eval a *
                v3.eval a +
              (36864 : k) * ((p.coeff 2).eval a) ^ 2 * w7.eval a +
            (61440 : k) * (p.coeff 2).eval a * (q.coeff 5).eval a *
                t1.eval a -
              (161280 : k) * (p.coeff 2).eval a * s2.eval a *
                (t1.eval a) ^ 4 +
            (258720 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 6 +
              (125440 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 3 *
                v3.eval a -
            (92160 : k) * (p.coeff 2).eval a * (t1.eval a) ^ 2 *
                w7.eval a -
              (25600 : k) * (q.coeff 5).eval a * (t1.eval a) ^ 3 +
            (29568 : k) * s2.eval a * (t1.eval a) ^ 6 -
              (45045 : k) * (t1.eval a) ^ 8 -
            (28224 : k) * (t1.eval a) ^ 5 * v3.eval a +
              (26880 : k) * (t1.eval a) ^ 4 * w7.eval a =
            0 := by
  obtain ⟨hp3pow, hq8pow, hq7pow, hq6pow, hq9pow, hmix5, hmix6, hjet⟩ :=
    nonzeroFace410_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4 hq10 hN hD hroot
  obtain ⟨eta, hY⟩ :=
    nonzeroFace410_eighthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  obtain ⟨t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot,
    hbroot⟩ := hjet
  have hmixroot : (t1.eval a) ^ 2 - (4 : k) * (p.coeff 2).eval a = 0 := by
    have hform :
        localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) =
          h0 ^ 4 * (t1 ^ 2 - (4 : k[X]) * p.coeff 2) := by
      simp only [localSixthMixed410, ht1]
      ring
    obtain ⟨rQ, hrQ⟩ := hmix6
    have hmixpoly :
        t1 ^ 2 - (4 : k[X]) * p.coeff 2 = h0 * rQ := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hh0)
      calc
        h0 ^ 4 * (t1 ^ 2 - (4 : k[X]) * p.coeff 2) =
            localSixthMixed410 h0 (p.coeff 3) (p.coeff 2) := hform.symm
        _ = h0 ^ 5 * rQ := hrQ
        _ = h0 ^ 4 * (h0 * rQ) := by ring
    have heval := congrArg (fun r : k[X] => r.eval a) hmixpoly
    simpa [hroot, eval_pow] using heval
  have hcompat :=
    eighthFace_rootCompatible_410 (t1.eval a) ((p.coeff 2).eval a)
      (s2.eval a) (v3.eval a) (w7.eval a) ((q.coeff 5).eval a)
      hsroot hvroot hwroot hbroot hmixroot
  exact ⟨⟨t1, ht1⟩, ⟨s2, hs2⟩, ⟨v3, hv3⟩, ⟨w7, hw7⟩, hq9pow, hmix5, hmix6,
    ⟨eta, hY⟩, t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot,
    hbroot, hmixroot, hcompat⟩

/-- Source-facing eighth integral for a normalized scale-two `(4,10)`
nonzero face. -/
theorem normalized410ScaleTwo_nonzeroFace_eighthDefectPowerRelation
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
        localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
            (q.coeff 2) lambda =
          Polynomial.C eta * h0 ^ 26 := by
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
  obtain ⟨eta, hY⟩ :=
    nonzeroFace410_eighthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4' hq10' hN' hD
  exact ⟨h0, lambda, eta, hh0, hlambda, hh0degree, hH, hN', hY⟩

/-- Finite local initial packet of a normalized scale-two `(4,10)`
nonzero face: the seventh-face jet together with the eighth integral
of weight twenty-six.  The degree-`5` leading form is compatible with
that jet and does not force `t₁(a) = 0`. -/
theorem normalized410ScaleTwo_nonzeroFace_eighthInitialPacket
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
        (∃ eta : K,
          localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
              (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
              (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
              (q.coeff 2) lambda =
            Polynomial.C eta * h0 ^ 26) ∧
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
  obtain ⟨hp3, hq8, hq7, hq6, hq9, hmix5, hmix6, hY, hjet⟩ :=
    nonzeroFace410_linearRoot_eighthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp4' hq10' hN' hD hroot
  obtain ⟨t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot,
    hbroot, _hmixroot, _hcompat⟩ := hjet
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp3, hq8, hq7,
    hq6, hq9, hmix5, hmix6, hY,
    ⟨t1, s2, v3, w7, ht1, hs2, hv3, hw7, hsroot, hvroot, hwroot, hbroot⟩,
    hN'⟩

end NonzeroEighthFace410

#print axioms eighthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_5_monicQuarticDecic
#print axioms eighthDefect_eq_clearedEta410
#print axioms eighthFace_rootCompatible_410
#print axioms nonzeroFace410_eighthDefectPowerRelation
#print axioms nonzeroFace410_linearRoot_eighthInitialPacket
#print axioms normalized410ScaleTwo_nonzeroFace_eighthDefectPowerRelation
#print axioms normalized410ScaleTwo_nonzeroFace_eighthInitialPacket

end Max11DegreeRoutes
