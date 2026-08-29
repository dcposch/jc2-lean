import LowScale610ScaleTwoSixthFace

/-! # Scale-two seventh face for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the sixth face supplies the degree-`9` integral
and the jet `h⁴ ∣ p₅`, `h² ∣ p₄`, `h⁶ ∣ q₈`, `h³ ∣ q₇`, `h ∣ q₆`,
`h⁸ ∣ q₉`.  The next Keller coefficient is the degree-`8` Jacobian
row.  After the same sextic depression that kills `z⁵`, that row is
`9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - D P' - 2 C Q' - 3 B R'
- 4 A S' - 6 U' = 0`.  The resulting first integral clears to a
polynomial defect `X` of weight thirty-five.

Evaluating the second through seventh defects together at the root of
`h` upgrades the jet to `h⁴ ∣ q₇` and `h² ∣ q₆`, and forces the finite
power identities `3 (p₄/h²)(a) = w²`, `9 (q₈/h⁶)(a) = 10 w²`,
`27 p₃(a) = w³`, `27 (q₇/h⁴)(a) = 10 w³`, `81 (q₆/h²)(a) = 5 w⁴`, and
`243 q₅(a) = w⁵` with `w = (p₅/h⁴)(a)`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  It is the source of the first mixed sextic/decic
`z⁰`/`z³` defect after the degree-`9` integral. -/
theorem seventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        (p.coeff 1 * Polynomial.C (1 : K)) * (q.coeff 8).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1),
        (8, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC2]
  linear_combination hcoeff

/-! ## Sextic `z⁰` and decic `z³` coordinates -/

section Depression610Seventh

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z³` coefficient. -/
def depressedU610 (h r b9 b8 b7 b6 b5 b4 b3 : F) : F :=
  -120 * r ^ 7 + 84 * (b9 / h ^ 9) * r ^ 6 -
    56 * (b8 / h ^ 8) * r ^ 5 + 35 * (b7 / h ^ 7) * r ^ 4 -
    20 * (b6 / h ^ 6) * r ^ 3 + 10 * (b5 / h ^ 5) * r ^ 2 -
    4 * (b4 / h ^ 4) * r + b3 / h ^ 3

/-- First residual of the degree-`8` row.  Equivalent to
`U - (3/2) L E - (4/3) α D - (7/6) β C - γ B - (5/6) δ A
- (10/9) A D - (10/9) B C - (4/9) α A B - (7/72) β A²
+ (5/27) A² B + (1/16) L A³ - (3/4) L A C - (3/8) L B²`
on the second-, third-, fourth-, and fifth-face integrals. -/
def zetaResidual610 (L A B C0 D0 E0 P Q R S0 U0 : F) : F :=
  U0 - (3 / 2 : F) * L * E0 -
    (4 / 3 : F) * alphaResidual610 A P * D0 -
    (7 / 6 : F) * betaResidual610 L A B Q * C0 -
    gammaResidual610 L A B C0 P R * B -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * A -
    (10 / 9 : F) * A * D0 - (10 / 9 : F) * B * C0 -
    (4 / 9 : F) * alphaResidual610 A P * A * B -
    (7 / 72 : F) * betaResidual610 L A B Q * A ^ 2 +
    (5 / 27 : F) * A ^ 2 * B + (1 / 16 : F) * L * A ^ 3 -
    (3 / 4 : F) * L * A * C0 - (3 / 8 : F) * L * B ^ 2

/-- Polynomial numerator of `3072 h³⁵ ζ` on the ninth-power face. -/
def localClearedSeventhDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : F[X]) (lambda : F) : F[X] :=
  (1536 : F[X]) * Polynomial.C lambda * a0 * h ^ 35 +
    (7680 : F[X]) * a1 * a4 * h ^ 30 +
    (1920 : F[X]) * a1 * a5 ^ 2 * h ^ 24 -
    (2304 : F[X]) * Polynomial.C lambda * a1 * a5 * h ^ 29 -
    (4096 : F[X]) * a1 * b8 * h ^ 26 +
    (7680 : F[X]) * a2 * a3 * h ^ 30 -
    (7680 : F[X]) * a2 * a4 * a5 * h ^ 24 -
    (2304 : F[X]) * Polynomial.C lambda * a2 * a4 * h ^ 29 -
    (3200 : F[X]) * a2 * a5 ^ 3 * h ^ 18 +
    (2880 : F[X]) * Polynomial.C lambda * a2 * a5 ^ 2 * h ^ 23 +
    (6144 : F[X]) * a2 * a5 * b8 * h ^ 20 -
    (3584 : F[X]) * a2 * b7 * h ^ 26 -
    (3840 : F[X]) * a3 ^ 2 * a5 * h ^ 24 -
    (1152 : F[X]) * Polynomial.C lambda * a3 ^ 2 * h ^ 29 -
    (9600 : F[X]) * a3 * a4 ^ 2 * h ^ 24 +
    (4800 : F[X]) * a3 * a4 * a5 ^ 2 * h ^ 18 +
    (5760 : F[X]) * Polynomial.C lambda * a3 * a4 * a5 * h ^ 23 +
    (6144 : F[X]) * a3 * a4 * b8 * h ^ 20 +
    (4200 : F[X]) * a3 * a5 ^ 4 * h ^ 12 -
    (3360 : F[X]) * Polynomial.C lambda * a3 * a5 ^ 3 * h ^ 17 -
    (7680 : F[X]) * a3 * a5 ^ 2 * b8 * h ^ 14 +
    (5376 : F[X]) * a3 * a5 * b7 * h ^ 20 -
    (3072 : F[X]) * a3 * b6 * h ^ 26 +
    (6400 : F[X]) * a4 ^ 3 * a5 * h ^ 18 +
    (960 : F[X]) * Polynomial.C lambda * a4 ^ 3 * h ^ 23 -
    (5040 : F[X]) * Polynomial.C lambda * a4 ^ 2 * a5 ^ 2 * h ^ 17 -
    (7680 : F[X]) * a4 ^ 2 * a5 * b8 * h ^ 14 +
    (2688 : F[X]) * a4 ^ 2 * b7 * h ^ 20 -
    (5040 : F[X]) * a4 * a5 ^ 5 * h ^ 6 +
    (3780 : F[X]) * Polynomial.C lambda * a4 * a5 ^ 4 * h ^ 11 +
    (8960 : F[X]) * a4 * a5 ^ 3 * b8 * h ^ 8 -
    (6720 : F[X]) * a4 * a5 ^ 2 * b7 * h ^ 14 +
    (4608 : F[X]) * a4 * a5 * b6 * h ^ 20 -
    (2560 : F[X]) * a4 * b5 * h ^ 26 +
    (1320 : F[X]) * a5 ^ 7 -
    (693 : F[X]) * Polynomial.C lambda * a5 ^ 6 * h ^ 5 -
    (2016 : F[X]) * a5 ^ 5 * b8 * h ^ 2 +
    (1960 : F[X]) * a5 ^ 4 * b7 * h ^ 8 -
    (1920 : F[X]) * a5 ^ 3 * b6 * h ^ 14 +
    (1920 : F[X]) * a5 ^ 2 * b5 * h ^ 20 -
    (2048 : F[X]) * a5 * b4 * h ^ 26 +
    (3072 : F[X]) * b3 * h ^ 32

/-- Exact denominator clearing for the decic `z³` coordinate on the
ninth-power face. -/
theorem depressedU610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 =
      (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
          84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
          1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
          7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
        (11664 * h ^ 35) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedU610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      -120 * (a5 / (6 * h ^ 5)) ^ 7 +
          84 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 6 -
        56 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 5 +
          35 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 4 -
        20 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 3 +
          10 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 2 -
        4 * (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) + b3 / h ^ 3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) := by
    field_simp [hh, h6, h3, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh35,
      h11664]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9, hh35,
      h11664]
    ring
  exact hrewrite

set_option maxHeartbeats 16000000 in
/-- Clearing the first integral
`U - (3/2) L E - (4/3) α D - (7/6) β C - γ B - (5/6) δ A
- (10/9) A D - (10/9) B C - (4/9) α A B - (7/72) β A²
+ (5/27) A² B + (1/16) L A³ - (3/4) L A C - (3/8) L B²`
against `h³⁵` on the ninth-power face. -/
theorem seventhDefect_eq_clearedZeta610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (3072 : F) * h ^ 35 *
        zetaResidual610
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
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3) =
      (1536 : F) * lambda * a0 * h ^ 35 + (7680 : F) * a1 * a4 * h ^ 30 +
        (1920 : F) * a1 * a5 ^ 2 * h ^ 24 -
        (2304 : F) * lambda * a1 * a5 * h ^ 29 -
        (4096 : F) * a1 * b8 * h ^ 26 + (7680 : F) * a2 * a3 * h ^ 30 -
        (7680 : F) * a2 * a4 * a5 * h ^ 24 -
        (2304 : F) * lambda * a2 * a4 * h ^ 29 -
        (3200 : F) * a2 * a5 ^ 3 * h ^ 18 +
        (2880 : F) * lambda * a2 * a5 ^ 2 * h ^ 23 +
        (6144 : F) * a2 * a5 * b8 * h ^ 20 -
        (3584 : F) * a2 * b7 * h ^ 26 -
        (3840 : F) * a3 ^ 2 * a5 * h ^ 24 -
        (1152 : F) * lambda * a3 ^ 2 * h ^ 29 -
        (9600 : F) * a3 * a4 ^ 2 * h ^ 24 +
        (4800 : F) * a3 * a4 * a5 ^ 2 * h ^ 18 +
        (5760 : F) * lambda * a3 * a4 * a5 * h ^ 23 +
        (6144 : F) * a3 * a4 * b8 * h ^ 20 +
        (4200 : F) * a3 * a5 ^ 4 * h ^ 12 -
        (3360 : F) * lambda * a3 * a5 ^ 3 * h ^ 17 -
        (7680 : F) * a3 * a5 ^ 2 * b8 * h ^ 14 +
        (5376 : F) * a3 * a5 * b7 * h ^ 20 -
        (3072 : F) * a3 * b6 * h ^ 26 +
        (6400 : F) * a4 ^ 3 * a5 * h ^ 18 +
        (960 : F) * lambda * a4 ^ 3 * h ^ 23 -
        (5040 : F) * lambda * a4 ^ 2 * a5 ^ 2 * h ^ 17 -
        (7680 : F) * a4 ^ 2 * a5 * b8 * h ^ 14 +
        (2688 : F) * a4 ^ 2 * b7 * h ^ 20 -
        (5040 : F) * a4 * a5 ^ 5 * h ^ 6 +
        (3780 : F) * lambda * a4 * a5 ^ 4 * h ^ 11 +
        (8960 : F) * a4 * a5 ^ 3 * b8 * h ^ 8 -
        (6720 : F) * a4 * a5 ^ 2 * b7 * h ^ 14 +
        (4608 : F) * a4 * a5 * b6 * h ^ 20 -
        (2560 : F) * a4 * b5 * h ^ 26 + (1320 : F) * a5 ^ 7 -
        (693 : F) * lambda * a5 ^ 6 * h ^ 5 -
        (2016 : F) * a5 ^ 5 * b8 * h ^ 2 +
        (1960 : F) * a5 ^ 4 * b7 * h ^ 8 -
        (1920 : F) * a5 ^ 3 * b6 * h ^ 14 +
        (1920 : F) * a5 ^ 2 * b5 * h ^ 20 -
        (2048 : F) * a5 * b4 * h ^ 26 +
        (3072 : F) * b3 * h ^ 32 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
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
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hU :
      depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  simp only [zetaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hU, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610]
  field_simp [hh, h2, h3, h4, h6, h8, h9, h12, h16, h18, h27, h54, h72,
    h81, h144, h216, h324, h432, h648, h11664, h46656, h93312, hh10,
    hh15, hh20, hh25, hh30, hh35]
  ring

end Depression610Seventh

/-! ## Degree-`8` depressed Jacobian coefficient -/

section DepressedRow610Seventh

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`8` Jacobian coefficient is
exactly `9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - D P' - 2 C Q'
- 3 B R' - 4 A S' - 6 U'`. -/
theorem differentialJacobian_coeff_8_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 8 =
      (9 : F) * g.coeff 9 * d (f.coeff 0) +
        (8 : F) * g.coeff 8 * d (f.coeff 1) +
        (7 : F) * g.coeff 7 * d (f.coeff 2) +
        (6 : F) * g.coeff 6 * d (f.coeff 3) +
        (5 : F) * g.coeff 5 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 8) -
          (2 : F) * f.coeff 2 * d (g.coeff 7) -
          (3 : F) * f.coeff 3 * d (g.coeff 6) -
          (4 : F) * f.coeff 4 * d (g.coeff 5) -
          (6 : F) * d (g.coeff 3) := by
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
  have hmem08 : ((0, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 8 =
        (9 : F) * g.coeff 9 * d (f.coeff 0) +
          (8 : F) * g.coeff 8 * d (f.coeff 1) +
          (7 : F) * g.coeff 7 * d (f.coeff 2) +
          (6 : F) * g.coeff 6 * d (f.coeff 3) +
          (5 : F) * g.coeff 5 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 8) : ℕ × ℕ) ≠ (1, 7) := by decide
    have hne08_26 : ((0, 8) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hne08_35 : ((0, 8) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne08_44 : ((0, 8) : ℕ × ℕ) ≠ (4, 4) := by decide
    have hne17_26 : ((1, 7) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hne17_35 : ((1, 7) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne17_44 : ((1, 7) : ℕ × ℕ) ≠ (4, 4) := by decide
    have hne26_35 : ((2, 6) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne26_44 : ((2, 6) : ℕ × ℕ) ≠ (4, 4) := by decide
    have hne35_44 : ((3, 5) : ℕ × ℕ) ≠ (4, 4) := by decide
    have hsubset :
        ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (8 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 8 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
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
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne35
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne44
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 4 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
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
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder8, hder7, hder6, hder5, hder4]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 8 =
        (1 : F) * f.coeff 1 * d (g.coeff 8) +
          (2 : F) * f.coeff 2 * d (g.coeff 7) +
          (3 : F) * f.coeff 3 * d (g.coeff 6) +
          (4 : F) * f.coeff 4 * d (g.coeff 5) +
          (6 : F) * d (g.coeff 3) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 8) : ℕ × ℕ) ≠ (1, 7) := by decide
    have hne08_26 : ((0, 8) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hne08_35 : ((0, 8) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne08_53 : ((0, 8) : ℕ × ℕ) ≠ (5, 3) := by decide
    have hne17_26 : ((1, 7) : ℕ × ℕ) ≠ (2, 6) := by decide
    have hne17_35 : ((1, 7) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne17_53 : ((1, 7) : ℕ × ℕ) ≠ (5, 3) := by decide
    have hne26_35 : ((2, 6) : ℕ × ℕ) ≠ (3, 5) := by decide
    have hne26_53 : ((2, 6) : ℕ × ℕ) ≠ (5, 3) := by decide
    have hne35_53 : ((3, 5) : ℕ × ℕ) ≠ (5, 3) := by decide
    have hsubset : ({(0, 8), (1, 7), (2, 6), (3, 5), (5, 3)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (8 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (8 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 8), (1, 7), (2, 6), (3, 5), (5, 3)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 8 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
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
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne35
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne53
            ext
            · exact h5
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 8), (1, 7), (2, 6), (3, 5), (5, 3)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 3 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_53]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_53]),
        Finset.sum_insert (by simp [hne26_35, hne26_53]),
        Finset.sum_insert (by simp [hne35_53]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
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
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem zetaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 U0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hrow : (9 : F) * L * d E0 + (8 : F) * P * d D0 +
        (7 : F) * Q * d C0 + (6 : F) * R * d B +
        (5 : F) * S0 * d A - (1 : F) * D0 * d P -
        (2 : F) * C0 * d Q - (3 : F) * B * d R -
        (4 : F) * A * d S0 - (6 : F) * d U0 = 0) :
    d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h16ne : (16 : F) ≠ 0 := by norm_num
  have h16inv : d (16 : F)⁻¹ = 0 := by
    have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
    have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
      rw [hone]
      exact d.map_one_eq_zero
    have hleib :
        d ((16 : F) * (16 : F)⁻¹) =
          (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
      Derivation.leibniz d (16 : F) (16 : F)⁻¹
    have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
      simpa [smul_eq_mul, hd1] using hleib.symm
    have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
      simpa [h16, mul_zero, add_zero] using hsum
    exact (mul_eq_zero.mp honly).resolve_left h16ne
  have h18 : d (18 : F) = 0 := d.map_natCast 18
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h72 : d (72 : F) = 0 := d.map_natCast 72
  have h10 : d (10 : F) = 0 := d.map_natCast 10
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h56 : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h109 : d (10 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h10]
  have h49 : d (4 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h4]
  have h772 : d (7 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h7]
  have h527 : d (5 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h5]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [div_eq_mul_inv, d.map_one_eq_zero, h16inv, zero_mul]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
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
  have hDlt0 :
      d S0 - (5 / 3 : F) * d D0 - (3 / 2 : F) * L * d C0 -
        (4 / 3 : F) * P * d B - (4 / 3 : F) * B * d P -
        (7 / 6 : F) * Q * d A - (7 / 6 : F) * A * d Q +
        (55 / 18 : F) * A * d B + (55 / 18 : F) * B * d A +
        (11 / 4 : F) * L * A * d A = 0 := by
    have hdelta' :
        d S0 - (5 / 3 : F) * d D0 - (3 / 2 : F) * L * d C0 -
          ((4 / 3 : F) * P * d B + B * ((4 / 3 : F) * d P)) -
          ((7 / 6 : F) * Q * d A + A * ((7 / 6 : F) * d Q)) +
          (55 / 18 : F) * (A * d B + B * d A) +
          (11 / 8 : F) * L * ((2 : F) * A * d A) = 0 := by
      have hsq : d (A * A) = (2 : F) * A * d A := by
        simp [Derivation.leibniz]
        ring
      have h5518 : d (55 / 18 : F) = 0 := by
        have h55 : d (55 : F) = 0 := d.map_natCast 55
        simp [Derivation.leibniz_div, h18, h55]
      have h118 : d (11 / 8 : F) = 0 := by
        have h11 : d (11 : F) = 0 := d.map_natCast 11
        simp [Derivation.leibniz_div, h8, h11]
      have hexp :
          deltaResidual610 L A B C0 D0 P Q S0 =
            S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
              (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
              (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
        simp only [deltaResidual610, alphaResidual610, betaResidual610,
          pow_two]
        ring
      have hdlt := hdelta
      rw [hexp] at hdlt
      simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
        h5518, h118, zero_mul, add_zero, mul_zero, hsq] at hdlt
      linear_combination hdlt
    linear_combination hdelta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]
    ring
  have hzeta :
      zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 =
        U0 - (3 / 2 : F) * L * E0 - (4 / 3 : F) * P * D0 -
          (7 / 6 : F) * Q * C0 - R * B - (5 / 6 : F) * S0 * A +
          (5 / 2 : F) * A * D0 + (5 / 2 : F) * B * C0 +
          (2 : F) * A * B * P + (7 / 8 : F) * Q * (A * A) +
          (9 / 4 : F) * L * A * C0 + (9 / 8 : F) * L * (B * B) -
          (25 / 8 : F) * (A * A) * B - (15 / 16 : F) * L * (A * A * A) := by
    simp only [zetaResidual610, alphaResidual610, betaResidual610,
      gammaResidual610, deltaResidual610, pow_two, pow_three]
    ring
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h258 : d (25 / 8 : F) = 0 := by
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    simp [Derivation.leibniz_div, h8, h25]
  have h1516 : d (15 / 16 : F) = 0 := by
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
      add_zero, mul_zero]
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hdLE : d ((3 / 2 : F) * L * E0) = (3 / 2 : F) * L * d E0 := by
    simp [Derivation.leibniz, smul_eq_mul, h32, hL, zero_mul, add_zero]
  have hdPD : d ((4 / 3 : F) * P * D0) =
      (4 / 3 : F) * (d P * D0 + P * d D0) := by
    simp [Derivation.leibniz, smul_eq_mul, h43]
    ring
  have hdQC : d ((7 / 6 : F) * Q * C0) =
      (7 / 6 : F) * (d Q * C0 + Q * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h76]
    ring
  have hdRB : d (R * B) = d R * B + R * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hdSA : d ((5 / 6 : F) * S0 * A) =
      (5 / 6 : F) * (d S0 * A + S0 * d A) := by
    simp [Derivation.leibniz, smul_eq_mul, h56]
    ring
  have hdAD : d ((5 / 2 : F) * A * D0) =
      (5 / 2 : F) * (d A * D0 + A * d D0) := by
    simp [Derivation.leibniz, smul_eq_mul, h52]
    ring
  have hdBC : d ((5 / 2 : F) * B * C0) =
      (5 / 2 : F) * (d B * C0 + B * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h52]
    ring
  have hdABP : d ((2 : F) * A * B * P) =
      (2 : F) * (d A * B * P + A * d B * P + A * B * d P) := by
    simp [Derivation.leibniz, smul_eq_mul, h2, zero_mul, add_zero]
    ring
  have hdQA2 : d ((7 / 8 : F) * Q * (A * A)) =
      (7 / 8 : F) * (d Q * (A * A) + Q * ((2 : F) * A * d A)) := by
    simp [Derivation.leibniz, smul_eq_mul, h78, hsq]
    ring
  have hdLAC : d ((9 / 4 : F) * L * A * C0) =
      (9 / 4 : F) * (L * d A * C0 + L * A * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h94, hL, zero_mul, add_zero]
    ring
  have hdLB2 : d ((9 / 8 : F) * L * (B * B)) =
      (9 / 8 : F) * (L * ((2 : F) * B * d B)) := by
    simp [Derivation.leibniz, smul_eq_mul, h98, hL, hsqB, zero_mul,
      add_zero]
    ring
  have hdA2B : d ((25 / 8 : F) * (A * A) * B) =
      (25 / 8 : F) * (((2 : F) * A * d A) * B + (A * A) * d B) := by
    simp [Derivation.leibniz, smul_eq_mul, h258, hsq]
    ring
  have hdLA3 : d ((15 / 16 : F) * L * (A * A * A)) =
      (15 / 16 : F) * (L * ((3 : F) * (A * A) * d A)) := by
    simp [Derivation.leibniz, smul_eq_mul, h1516, hL, hcub, zero_mul,
      add_zero]
    ring
  rw [hzeta]
  simp only [map_sub, map_add, hdLE, hdPD, hdQC, hdRB, hdSA, hdAD, hdBC,
    hdABP, hdQA2, hdLAC, hdLB2, hdA2B, hdLA3]
  linear_combination (-1 / 6 : F) * hrow +
    (-(2 : F) * A * B - (3 / 2 : F) * D0) * hP0 +
    (-(7 / 8 : F) * (A * A) - (3 / 2 : F) * C0) * hQ0 +
    (-(3 / 2 : F) * B) * hG0 + (-(3 / 2 : F) * A) * hDlt0

end DepressedRow610Seventh

/-! ## Affine depression of a degree-ten source, `z³` coefficient -/

section AffineDecic610Seventh

variable {k : Type*} [Field k] [CharZero k]

/-- The `z³` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff3_610
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
    · subst n
      simp
    · have : 4 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h4 | hlt4
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
    field_simp [hh]
    ring
  have h9_3 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 3 =
        84 * (p.coeff 9 / h ^ 9) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 3 hh]
    have hle : (3 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 3 = 84 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h8_3 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -56 * (p.coeff 8 / h ^ 8) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 3 hh]
    have hle : (3 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 3 = 56 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h7_3 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 3 =
        35 * (p.coeff 7 / h ^ 7) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 3 hh]
    have hle : (3 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 3 = 35 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]
    ring
  have h6_3 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -20 * (p.coeff 6 / h ^ 6) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 3 hh]
    have hle : (3 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 3 = 20 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]
    ring
  have h5_3 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 3 =
        10 * (p.coeff 5 / h ^ 5) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 3 hh]
    have hle : (3 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 3 = 10 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]
    ring
  have h4_3 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 3 =
        -4 * (p.coeff 4 / h ^ 4) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 3 hh]
    have hle : (3 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 3 = 4 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]
    ring
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

end AffineDecic610Seventh

/-! ## Local scalar identities at a simple root -/

section SeventhFaceScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- The sixth-face jet reduces the third and fourth defects at the root
of `h` to `u₇ = 0` and `b₆s = 0`. -/
theorem seventhFace_firstPass_vanish610
    (u7 b6s w : F)
    (hT : (648 : F) * u7 = 0)
    (hU : (432 : F) * b6s - (504 : F) * u7 * w = 0) :
    u7 = 0 ∧ b6s = 0 := by
  have h648 : (648 : F) ≠ 0 := by norm_num
  have hu0 : u7 = 0 := (mul_eq_zero.mp hT).resolve_left h648
  have h432 : (432 : F) ≠ 0 := by norm_num
  have hb0 : b6s = 0 := by
    have : (432 : F) * b6s = 0 := by
      simpa [hu0] using hU
    exact (mul_eq_zero.mp this).resolve_left h432
  exact ⟨hu0, hb0⟩

end SeventhFaceScalars610

/-! ## Source-facing seventh-face packet -/

section NonzeroSeventhFace610

variable {k : Type*} [Field k] [CharZero k]

/-- The sixth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h³⁵`. -/
theorem nonzeroFace610_seventhDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda =
        Polynomial.C eta * h0 ^ 35 := by
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
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
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
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg3 :
      g.coeff 3 =
        depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
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
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
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
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 (by simpa using hrow8)
  obtain ⟨eta0, heta0⟩ :
      ∃ a : k,
        zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 3) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hzeta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda) =
        (3072 : RatFunc k) * hRF ^ 35 *
          zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 3) := by
    have hF := seventhDefect_eq_clearedZeta610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedSeventhDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, zetaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610, hf4, hf3, hf2,
      hf1, hf0, hg3, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (3072 * eta0) * h0 ^ 35) := by
    rw [hclear, heta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨3072 * eta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides `q₇` to
order four and `q₆` to order two, and the remaining sixth-face
coordinates satisfy the root quadratic `18 s - 30 a₄s = 10 w²`. -/
theorem nonzeroFace610_linearRoot_seventhInitialPacket
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
      h0 ^ 6 ∣ q.coeff 8 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
      h0 ^ 2 ∣ q.coeff 6 ∧ h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨_eta, _hXrel⟩ :=
    nonzeroFace610_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨hp5pow, hp4div, hq8pow, hq7pow, hq6div, hq9pow⟩ :=
    nonzeroFace610_linearRoot_sixthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot
  obtain ⟨w, hw⟩ := hp5pow
  obtain ⟨a4s, ha4s⟩ := hp4div
  obtain ⟨s, hs⟩ := hq8pow
  obtain ⟨u7, hu7⟩ := hq7pow
  obtain ⟨b6s, hb6s⟩ := hq6div
  have hT0 :
      (648 : k[X]) * u7 - (1080 : k[X]) * p.coeff 3 * h0 +
          (720 : k[X]) * a4s * w * h0 - (864 : k[X]) * s * w * h0 +
        (520 : k[X]) * w ^ 3 * h0 +
          (324 : k[X]) * Polynomial.C lambda * a4s * h0 ^ 2 -
        (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 2 =
        Polynomial.C gamma * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 11 hh0)
    calc
      h0 ^ 11 *
            ((648 : k[X]) * u7 - (1080 : k[X]) * p.coeff 3 * h0 +
                (720 : k[X]) * a4s * w * h0 - (864 : k[X]) * s * w * h0 +
              (520 : k[X]) * w ^ 3 * h0 +
                (324 : k[X]) * Polynomial.C lambda * a4s * h0 ^ 2 -
              (351 : k[X]) * Polynomial.C lambda * w ^ 2 * h0 ^ 2) =
          localClearedThirdDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect610, hw, ha4s, hs, hu7]
        ring
      _ = Polynomial.C gamma * h0 ^ 15 := hT
      _ = h0 ^ 11 * (Polynomial.C gamma * h0 ^ 4) := by ring
  have hU0 :
      (432 : k[X]) * b6s - (504 : k[X]) * u7 * w +
        (720 : k[X]) * a4s ^ 2 * h0 - (576 : k[X]) * a4s * s * h0 +
          (360 : k[X]) * p.coeff 3 * w * h0 +
            (576 : k[X]) * s * w ^ 2 * h0 -
          (360 : k[X]) * w ^ 4 * h0 +
            (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 2 -
          (432 : k[X]) * Polynomial.C lambda * a4s * w * h0 ^ 2 +
            (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 2 -
          (720 : k[X]) * p.coeff 2 * h0 ^ 3 =
        Polynomial.C delta * h0 ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 15 hh0)
    calc
      h0 ^ 15 *
            ((432 : k[X]) * b6s - (504 : k[X]) * u7 * w +
              (720 : k[X]) * a4s ^ 2 * h0 - (576 : k[X]) * a4s * s * h0 +
                (360 : k[X]) * p.coeff 3 * w * h0 +
                  (576 : k[X]) * s * w ^ 2 * h0 -
                (360 : k[X]) * w ^ 4 * h0 +
                  (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 2 -
                (432 : k[X]) * Polynomial.C lambda * a4s * w * h0 ^ 2 +
                  (216 : k[X]) * Polynomial.C lambda * w ^ 3 * h0 ^ 2 -
                (720 : k[X]) * p.coeff 2 * h0 ^ 3) =
          localClearedFourthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect610, hw, ha4s, hs, hu7, hb6s]
        ring
      _ = Polynomial.C delta * h0 ^ 20 := hU
      _ = h0 ^ 15 * (Polynomial.C delta * h0 ^ 5) := by ring
  have hTroot : (648 : k) * u7.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (432 : k) * b6s.eval a - (504 : k) * u7.eval a * w.eval a =
      0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  obtain ⟨hu0, hb0⟩ :=
    seventhFace_firstPass_vanish610 (u7.eval a) (b6s.eval a) (w.eval a)
      hTroot hUroot
  have hu7_div : h0 ∣ u7 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 u7 a hh0degree hroot hu0
  have hb6s_div : h0 ∣ b6s :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 b6s a hh0degree hroot hb0
  have hq7pow4 : h0 ^ 4 ∣ q.coeff 7 := by
    obtain ⟨u8, hu8⟩ := hu7_div
    refine ⟨u8, ?_⟩
    rw [hu7, hu8]
    ring
  have hq6pow2 : h0 ^ 2 ∣ q.coeff 6 := by
    obtain ⟨b62, hb62⟩ := hb6s_div
    refine ⟨b62, ?_⟩
    rw [hb6s, hb62]
    ring
  exact ⟨⟨w, hw⟩, ⟨a4s, ha4s⟩, ⟨s, hs⟩, hq7pow4, hq6pow2, hq9pow⟩

/-- Source-facing seventh integral for a normalized scale-two `(6,10)`
nonzero face. -/
theorem normalized610ScaleTwo_nonzeroFace_seventhDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSeventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda =
          Polynomial.C eta * h0 ^ 35 := by
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
  obtain ⟨eta, hX⟩ :=
    nonzeroFace610_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6' hq10' hN' hD
  exact ⟨h0, lambda, eta, hh0, hlambda, hh0degree, hH, hN', hX⟩

/-- Finite local initial packet of a normalized scale-two `(6,10)`
nonzero face: the seventh-face jet `h⁴ ∣ p₅`, `h² ∣ p₄`, `h⁶ ∣ q₈`,
`h⁴ ∣ q₇`, `h² ∣ q₆`, and `h⁸ ∣ q₉`. -/
theorem normalized610ScaleTwo_nonzeroFace_seventhInitialPacket
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
        h0 ^ 6 ∣ q.coeff 8 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
        h0 ^ 2 ∣ q.coeff 6 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
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
    nonzeroFace610_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp5, hp4, hq8,
    hq7, hq6, hq9, hN'⟩

end NonzeroSeventhFace610

#print axioms seventhCoefficientJacobianRow_610
#print axioms differentialJacobian_coeff_8_monicSexticDecic
#print axioms seventhDefect_eq_clearedZeta610
#print axioms nonzeroFace610_seventhDefectPowerRelation
#print axioms nonzeroFace610_linearRoot_seventhInitialPacket
#print axioms normalized610ScaleTwo_nonzeroFace_seventhDefectPowerRelation
#print axioms normalized610ScaleTwo_nonzeroFace_seventhInitialPacket
#print axioms seventhFace_firstPass_vanish610

end Max11DegreeRoutes
