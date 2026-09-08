import LowScale810ScaleTwoFifthFace

/-! # Scale-two sixth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the fifth face supplies the degree-`12` integral
and the local jet `h⁶ ∣ p₇`, `h³ ∣ p₆`, `h⁵ ∣ q₈`, `h² ∣ q₇`,
`h⁸ ∣ q₉`.  The next Keller coefficient is the degree-`11` Jacobian
row.  After the same octic depression that kills `z⁷`, that row is
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 4 C P' - 5 B Q' - 6 A R' - 8 T' = 0`.
The resulting first integral clears to a polynomial defect `W` of
weight forty-two.

Evaluating the third and sixth defects together at the root of `h`
forces the finite initial jet `h⁶ ∣ p₇`, `h³ ∣ p₆`, `h ∣ p₅`,
`h⁵ ∣ q₈`, `h³ ∣ q₇`, and `h⁸ ∣ q₉`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The sixth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  It is the source of the first mixed octic/decic
`z²`/`z⁴` defect after the degree-`12` integral. -/
theorem sixthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 7).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 4).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 5).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 6).derivative +
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC8, hC9, hC10, hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Octic `z²` and decic `z⁴` coordinates -/

section Depression810Sixth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z²` coefficient. -/
def depressedE810 (h r a7 a6 a5 a4 a3 a2 : F) : F :=
  depressedT68 h r a7 a6 a5 a4 a3 a2

/-- Depressed decic `z⁴` coefficient. -/
def depressedT810 (h r b9 b8 b7 b6 b5 b4 : F) : F :=
  210 * r ^ 6 - 126 * (b9 / h ^ 9) * r ^ 5 +
    70 * (b8 / h ^ 8) * r ^ 4 - 35 * (b7 / h ^ 7) * r ^ 3 +
    15 * (b6 / h ^ 6) * r ^ 2 - 5 * (b5 / h ^ 5) * r + b4 / h ^ 4

/-- First residual of the degree-`11` row. -/
def epsilonResidual810 (L A B C0 D0 E0 P Q R T0 : F) : F :=
  T0 - ((5 / 4 : F) * E0 + (5 / 32 : F) * B ^ 2 +
    (5 / 16 : F) * A * C0 - (5 / 128 : F) * A ^ 3 +
    L * ((9 / 8 : F) * D0 + (9 / 64 : F) * A * B) +
    alphaResidual810 A P * C0 +
    (7 / 8 : F) * betaResidual810 L A B Q * B +
    (3 / 4 : F) * gammaResidual810 L A B C0 P R * A)

/-- Polynomial numerator of `131072 h⁴² ε` on the ninth-power face. -/
def localClearedSixthDefect810
    (h a7 a6 a5 a4 a3 a2 b8 b7 b6 b5 b4 : F[X]) (lambda : F) : F[X] :=
  -(163840 : F[X]) * a2 * h ^ 40 +
    (61440 : F[X]) * a3 * a7 * h ^ 32 +
    (36864 : F[X]) * Polynomial.C lambda * a3 * h ^ 39 +
    (245760 : F[X]) * a4 * a6 * h ^ 32 -
    (30720 : F[X]) * a4 * a7 ^ 2 * h ^ 24 -
    (55296 : F[X]) * Polynomial.C lambda * a4 * a7 * h ^ 31 -
    (131072 : F[X]) * a4 * b8 * h ^ 30 +
    (122880 : F[X]) * a5 ^ 2 * h ^ 32 -
    (337920 : F[X]) * a5 * a6 * a7 * h ^ 24 -
    (55296 : F[X]) * Polynomial.C lambda * a5 * a6 * h ^ 31 +
    (12800 : F[X]) * a5 * a7 ^ 3 * h ^ 16 +
    (69120 : F[X]) * Polynomial.C lambda * a5 * a7 ^ 2 * h ^ 23 +
    (196608 : F[X]) * a5 * a7 * b8 * h ^ 22 -
    (114688 : F[X]) * a5 * b7 * h ^ 30 -
    (102400 : F[X]) * a6 ^ 3 * h ^ 24 +
    (192000 : F[X]) * a6 ^ 2 * a7 ^ 2 * h ^ 16 +
    (69120 : F[X]) * Polynomial.C lambda * a6 ^ 2 * a7 * h ^ 23 +
    (98304 : F[X]) * a6 ^ 2 * b8 * h ^ 22 -
    (80640 : F[X]) * Polynomial.C lambda * a6 * a7 ^ 3 * h ^ 15 -
    (245760 : F[X]) * a6 * a7 ^ 2 * b8 * h ^ 14 +
    (172032 : F[X]) * a6 * a7 * b7 * h ^ 22 -
    (98304 : F[X]) * a6 * b6 * h ^ 30 -
    (16800 : F[X]) * a7 ^ 6 +
    (18144 : F[X]) * Polynomial.C lambda * a7 ^ 5 * h ^ 7 +
    (71680 : F[X]) * a7 ^ 4 * b8 * h ^ 6 -
    (71680 : F[X]) * a7 ^ 3 * b7 * h ^ 14 +
    (73728 : F[X]) * a7 ^ 2 * b6 * h ^ 22 -
    (81920 : F[X]) * a7 * b5 * h ^ 30 +
    (131072 : F[X]) * b4 * h ^ 38

theorem coeff_depressedOctic68_two
    (L P Q R S T0 U V : F) :
    (depressedOctic68 L P Q R S T0 U V).coeff 2 = T0 := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z²` coordinate. -/
theorem depressedE810_eq_cleared
    (h a7 a6 a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
      (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
          6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
          240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
        (65536 * h ^ 42) := by
  simp only [depressedE810, depressedT68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁴` coordinate on the
ninth-power face. -/
theorem depressedT810_eq_cleared
    (h a7 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
      (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
          2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
          30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
          131072 * b4 * h ^ 38) /
        (131072 * h ^ 42) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedT810, octicDepressionR810]
  have hrewrite :
      210 * (a7 / (8 * h ^ 7)) ^ 6 -
          126 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 5 +
        70 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 4 -
          35 * (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) ^ 3 +
        15 * (b6 / h ^ 6) * (a7 / (8 * h ^ 7)) ^ 2 -
          5 * (b5 / h ^ 5) * (a7 / (8 * h ^ 7)) + b4 / h ^ 4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) := by
    field_simp [hh, h8, hh2, hh4, hh5, hh6, hh7, hh8pow, hh9, hh42,
      h131072]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      have h4 : (4 : F) ≠ 0 := by norm_num
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, hh2, hh4, hh5, hh6, hh7, hh8pow, hh9, hh42,
      h131072]
    ring
  exact hrewrite

set_option maxHeartbeats 8000000 in
/-- Clearing the first integral
`T - (5/4) E - (5/32) B² - (5/16) A C + (5/128) A³
  - L ((9/8) D + (9/64) A B) - α C - (7/8) β B - (3/4) γ A`
against `h⁴²` on the ninth-power face. -/
theorem sixthDefect_eq_clearedEpsilon810
    (h a7 a6 a5 a4 a3 a2 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (131072 : F) * h ^ 42 *
        epsilonResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4) =
      -(163840 : F) * a2 * h ^ 40 + (61440 : F) * a3 * a7 * h ^ 32 +
        (36864 : F) * lambda * a3 * h ^ 39 +
        (245760 : F) * a4 * a6 * h ^ 32 -
        (30720 : F) * a4 * a7 ^ 2 * h ^ 24 -
        (55296 : F) * lambda * a4 * a7 * h ^ 31 -
        (131072 : F) * a4 * b8 * h ^ 30 +
        (122880 : F) * a5 ^ 2 * h ^ 32 -
        (337920 : F) * a5 * a6 * a7 * h ^ 24 -
        (55296 : F) * lambda * a5 * a6 * h ^ 31 +
        (12800 : F) * a5 * a7 ^ 3 * h ^ 16 +
        (69120 : F) * lambda * a5 * a7 ^ 2 * h ^ 23 +
        (196608 : F) * a5 * a7 * b8 * h ^ 22 -
        (114688 : F) * a5 * b7 * h ^ 30 -
        (102400 : F) * a6 ^ 3 * h ^ 24 +
        (192000 : F) * a6 ^ 2 * a7 ^ 2 * h ^ 16 +
        (69120 : F) * lambda * a6 ^ 2 * a7 * h ^ 23 +
        (98304 : F) * a6 ^ 2 * b8 * h ^ 22 -
        (80640 : F) * lambda * a6 * a7 ^ 3 * h ^ 15 -
        (245760 : F) * a6 * a7 ^ 2 * b8 * h ^ 14 +
        (172032 : F) * a6 * a7 * b7 * h ^ 22 -
        (98304 : F) * a6 * b6 * h ^ 30 - (16800 : F) * a7 ^ 6 +
        (18144 : F) * lambda * a7 ^ 5 * h ^ 7 +
        (71680 : F) * a7 ^ 4 * b8 * h ^ 6 -
        (71680 : F) * a7 ^ 3 * b7 * h ^ 14 +
        (73728 : F) * a7 ^ 2 * b6 * h ^ 22 -
        (81920 : F) * a7 * b5 * h ^ 30 +
        (131072 : F) * b4 * h ^ 38 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hL :
      depressedL810 h (octicDepressionR810 h a7) b9 = -lambda / 4 :=
    depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN
  have hA :
      depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / (16 * h ^ 14) :=
    depressedA810_eq_cleared h a7 a6 hh
  have hB :
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) /
          (32 * h ^ 21) :=
    depressedB810_eq_cleared h a7 a6 a5 hh
  have hC :
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
            480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) /
          (2048 * h ^ 28) :=
    depressedC810_eq_cleared h a7 a6 a5 a4 hh
  have hD0 :
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
            160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
            7 * a7 ^ 5) /
          (1024 * h ^ 35) :=
    depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh
  have hE0 :
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
        (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
            6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
            240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) /
          (65536 * h ^ 42) :=
    depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh
  have hP :
      depressedP810 h (octicDepressionR810 h a7) b9 b8 =
        (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
          (64 * h ^ 14) :=
    depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN
  have hQ :
      depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
        (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
            9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) /
          (64 * h ^ 21) :=
    depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN
  have hR :
      depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
        (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
            896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
            2048 * b6 * h ^ 22) /
          (2048 * h ^ 28) :=
    depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have h16A :
      (16 : F) * h ^ 14 *
          depressedA810 h (octicDepressionR810 h a7) a7 a6 =
        (16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2 := by
    rw [hA]
    field_simp [hh, h16, hh14]
  have h32B :
      (32 : F) * h ^ 21 *
          depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
        (32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
          (7 : F) * a7 ^ 3 := by
    rw [hB]
    field_simp [hh, h32, hh21]
  have h2048C :
      (2048 : F) * h ^ 28 *
          depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (2048 : F) * a4 * h ^ 24 - (1280 : F) * a5 * a7 * h ^ 16 +
          (480 : F) * a6 * a7 ^ 2 * h ^ 8 - (105 : F) * a7 ^ 4 := by
    rw [hC]
    field_simp [hh, h2048, hh28]
  have h1024D :
      (1024 : F) * h ^ 35 *
          depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (1024 : F) * a3 * h ^ 32 - (512 : F) * a4 * a7 * h ^ 24 +
          (160 : F) * a5 * a7 ^ 2 * h ^ 16 -
          (40 : F) * a6 * a7 ^ 3 * h ^ 8 + (7 : F) * a7 ^ 5 := by
    rw [hD0]
    field_simp [hh, h1024, hh35]
  have h65536E :
      (65536 : F) * h ^ 42 *
          depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3
            a2 =
        (65536 : F) * a2 * h ^ 40 - (24576 : F) * a3 * a7 * h ^ 32 +
          (6144 : F) * a4 * a7 ^ 2 * h ^ 24 -
          (1280 : F) * a5 * a7 ^ 3 * h ^ 16 +
          (240 : F) * a6 * a7 ^ 4 * h ^ 8 - (35 : F) * a7 ^ 6 := by
    rw [hE0]
    field_simp [hh, h65536, hh42]
  have h131072T :
      (131072 : F) * h ^ 42 *
          depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5
            b4 =
        -(525 : F) * a7 ^ 6 + (126 : F) * lambda * a7 ^ 5 * h ^ 7 +
          (2240 : F) * a7 ^ 4 * b8 * h ^ 6 -
          (8960 : F) * a7 ^ 3 * b7 * h ^ 14 +
          (30720 : F) * a7 ^ 2 * b6 * h ^ 22 -
          (81920 : F) * a7 * b5 * h ^ 30 +
          (131072 : F) * b4 * h ^ 38 := by
    rw [hT0]
    field_simp [hh, h131072, hh42]
  have h32alpha :
      (32 : F) * h ^ 14 *
          alphaResidual810
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedP810 h (octicDepressionR810 h a7) b9 b8) =
        (32 : F) * b8 * h ^ 6 - (40 : F) * a6 * h ^ 8 +
          (9 : F) * lambda * a7 * h ^ 7 - (5 : F) * a7 ^ 2 :=
    secondDefect_eq_clearedAlpha810 h a7 a6 b9 b8 lambda hh hN
  have h512beta :
      (512 : F) * h ^ 21 *
          betaResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7) =
        (100 : F) * a7 ^ 3 - (512 : F) * a7 * b8 * h ^ 6 -
          (135 : F) * lambda * a7 ^ 2 * h ^ 7 +
          (480 : F) * a6 * a7 * h ^ 8 + (512 : F) * b7 * h ^ 14 +
          (144 : F) * lambda * a6 * h ^ 15 -
          (640 : F) * a5 * h ^ 16 :=
    thirdDefect_eq_clearedBeta810 h a7 a6 a5 b9 b8 b7 lambda hh hN
  have h2048gamma :
      (2048 : F) * h ^ 28 *
          gammaResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
            (depressedP810 h (octicDepressionR810 h a7) b9 b8)
            (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7
              b6) =
        -(2560 : F) * a4 * h ^ 24 + (1600 : F) * a5 * a7 * h ^ 16 +
          (576 : F) * lambda * a5 * h ^ 23 +
          (2240 : F) * a6 ^ 2 * h ^ 16 -
          (1120 : F) * a6 * a7 ^ 2 * h ^ 8 -
          (1008 : F) * lambda * a6 * a7 * h ^ 15 -
          (2048 : F) * a6 * b8 * h ^ 14 - (385 : F) * a7 ^ 4 +
          (462 : F) * lambda * a7 ^ 3 * h ^ 7 +
          (1792 : F) * a7 ^ 2 * b8 * h ^ 6 -
          (1792 : F) * a7 * b7 * h ^ 14 +
          (2048 : F) * b6 * h ^ 22 :=
    fourthDefect_eq_clearedGamma810 h a7 a6 a5 a4 b9 b8 b7 b6 lambda
      hh hN
  have h163840E :
      (163840 : F) * h ^ 42 *
          depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3
            a2 =
        (5 / 2 : F) *
          ((65536 : F) * a2 * h ^ 40 -
            (24576 : F) * a3 * a7 * h ^ 32 +
            (6144 : F) * a4 * a7 ^ 2 * h ^ 24 -
            (1280 : F) * a5 * a7 ^ 3 * h ^ 16 +
            (240 : F) * a6 * a7 ^ 4 * h ^ 8 -
            (35 : F) * a7 ^ 6) := by
    have hscale :
        (163840 : F) * h ^ 42 *
            depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 a2 =
          (5 / 2 : F) *
            ((65536 : F) * h ^ 42 *
              depressedE810 h (octicDepressionR810 h a7) a7 a6 a5
                a4 a3 a2) := by
      ring
    rw [hscale, h65536E]
  have h36864D :
      (36864 : F) * lambda * h ^ 42 *
          depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
            a3 =
        (36 : F) * lambda * h ^ 7 *
          ((1024 : F) * a3 * h ^ 32 - (512 : F) * a4 * a7 * h ^ 24 +
            (160 : F) * a5 * a7 ^ 2 * h ^ 16 -
            (40 : F) * a6 * a7 ^ 3 * h ^ 8 +
            (7 : F) * a7 ^ 5) := by
    have hscale :
        (36864 : F) * lambda * h ^ 42 *
            depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 =
          (36 : F) * lambda * h ^ 7 *
            ((1024 : F) * h ^ 35 *
              depressedD810 h (octicDepressionR810 h a7) a7 a6 a5
                a4 a3) := by
      ring
    rw [hscale, h1024D]
  have h4608AB :
      (4608 : F) * lambda * h ^ 42 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
        (9 : F) * lambda * h ^ 7 *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) *
            ((32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
              (7 : F) * a7 ^ 3) := by
    have hscale :
        (4608 : F) * lambda * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5) =
          (9 : F) * lambda * h ^ 7 *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7 a6) *
              ((32 : F) * h ^ 21 *
                depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5) := by
      ring
    rw [hscale, h16A, h32B]
  have h5120A3 :
      (5120 : F) * h ^ 42 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 3 =
        (5 / 4 : F) *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) ^ 3 := by
    have hscale :
        (5120 : F) * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 3 =
          (5 / 4 : F) *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7
                  a6) ^ 3 := by
      field_simp [hh, h16, hh14, hh42]
      ring
    rw [hscale, h16A]
  have h40960AC :
      (40960 : F) * h ^ 42 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
            depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
              a4) =
        (5 / 4 : F) *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) *
            ((2048 : F) * a4 * h ^ 24 - (1280 : F) * a5 * a7 * h ^ 16 +
              (480 : F) * a6 * a7 ^ 2 * h ^ 8 -
              (105 : F) * a7 ^ 4) := by
    have hscale :
        (40960 : F) * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4) =
          (5 / 4 : F) *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7 a6) *
              ((2048 : F) * h ^ 28 *
                depressedC810 h (octicDepressionR810 h a7) a7 a6
                  a5 a4) := by
      ring
    rw [hscale, h16A, h2048C]
  have h20480B2 :
      (20480 : F) * h ^ 42 *
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) ^ 2 =
        (20 : F) *
          ((32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
            (7 : F) * a7 ^ 3) ^ 2 := by
    have hscale :
        (20480 : F) * h ^ 42 *
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) ^
              2 =
          (20 : F) *
            ((32 : F) * h ^ 21 *
                depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5) ^ 2 := by
      ring
    rw [hscale, h32B]
  have h131072alphaC :
      (131072 : F) * h ^ 42 *
          (alphaResidual810
              (depressedA810 h (octicDepressionR810 h a7) a7 a6)
              (depressedP810 h (octicDepressionR810 h a7) b9 b8) *
            depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
              a4) =
        (2 : F) *
          ((32 : F) * b8 * h ^ 6 - (40 : F) * a6 * h ^ 8 +
              (9 : F) * lambda * a7 * h ^ 7 - (5 : F) * a7 ^ 2) *
            ((2048 : F) * a4 * h ^ 24 - (1280 : F) * a5 * a7 * h ^ 16 +
              (480 : F) * a6 * a7 ^ 2 * h ^ 8 -
              (105 : F) * a7 ^ 4) := by
    have hscale :
        (131072 : F) * h ^ 42 *
            (alphaResidual810
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedP810 h (octicDepressionR810 h a7) b9
                  b8) *
              depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4) =
          (2 : F) *
            ((32 : F) * h ^ 14 *
                alphaResidual810
                  (depressedA810 h (octicDepressionR810 h a7) a7
                    a6)
                  (depressedP810 h (octicDepressionR810 h a7) b9
                    b8)) *
              ((2048 : F) * h ^ 28 *
                depressedC810 h (octicDepressionR810 h a7) a7 a6
                  a5 a4) := by
      ring
    rw [hscale, h32alpha, h2048C]
  have h114688betaB :
      (114688 : F) * h ^ 42 *
          (betaResidual810
              (depressedL810 h (octicDepressionR810 h a7) b9)
              (depressedA810 h (octicDepressionR810 h a7) a7 a6)
              (depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5)
              (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                b7) *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
        (7 : F) *
          ((100 : F) * a7 ^ 3 - (512 : F) * a7 * b8 * h ^ 6 -
              (135 : F) * lambda * a7 ^ 2 * h ^ 7 +
              (480 : F) * a6 * a7 * h ^ 8 + (512 : F) * b7 * h ^ 14 +
              (144 : F) * lambda * a6 * h ^ 15 -
              (640 : F) * a5 * h ^ 16) *
            ((32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
              (7 : F) * a7 ^ 3) := by
    have hscale :
        (114688 : F) * h ^ 42 *
            (betaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                  b7) *
              depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5) =
          (7 : F) *
            ((512 : F) * h ^ 21 *
                betaResidual810
                  (depressedL810 h (octicDepressionR810 h a7) b9)
                  (depressedA810 h (octicDepressionR810 h a7) a7
                    a6)
                  (depressedB810 h (octicDepressionR810 h a7) a7
                    a6 a5)
                  (depressedQ810 h (octicDepressionR810 h a7) b9
                    b8 b7)) *
              ((32 : F) * h ^ 21 *
                depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5) := by
      ring
    rw [hscale, h512beta, h32B]
  have h98304gammaA :
      (98304 : F) * h ^ 42 *
          (gammaResidual810
              (depressedL810 h (octicDepressionR810 h a7) b9)
              (depressedA810 h (octicDepressionR810 h a7) a7 a6)
              (depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5)
              (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4)
              (depressedP810 h (octicDepressionR810 h a7) b9 b8)
              (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7
                b6) *
            depressedA810 h (octicDepressionR810 h a7) a7 a6) =
        (3 : F) *
          (-(2560 : F) * a4 * h ^ 24 + (1600 : F) * a5 * a7 * h ^ 16 +
              (576 : F) * lambda * a5 * h ^ 23 +
              (2240 : F) * a6 ^ 2 * h ^ 16 -
              (1120 : F) * a6 * a7 ^ 2 * h ^ 8 -
              (1008 : F) * lambda * a6 * a7 * h ^ 15 -
              (2048 : F) * a6 * b8 * h ^ 14 - (385 : F) * a7 ^ 4 +
              (462 : F) * lambda * a7 ^ 3 * h ^ 7 +
              (1792 : F) * a7 ^ 2 * b8 * h ^ 6 -
              (1792 : F) * a7 * b7 * h ^ 14 +
              (2048 : F) * b6 * h ^ 22) *
            ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) := by
    have hscale :
        (98304 : F) * h ^ 42 *
            (gammaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedC810 h (octicDepressionR810 h a7) a7 a6
                  a5 a4)
                (depressedP810 h (octicDepressionR810 h a7) b9
                  b8)
                (depressedR810 h (octicDepressionR810 h a7) b9 b8
                  b7 b6) *
              depressedA810 h (octicDepressionR810 h a7) a7 a6) =
          (3 : F) *
            ((2048 : F) * h ^ 28 *
                gammaResidual810
                  (depressedL810 h (octicDepressionR810 h a7) b9)
                  (depressedA810 h (octicDepressionR810 h a7) a7
                    a6)
                  (depressedB810 h (octicDepressionR810 h a7) a7
                    a6 a5)
                  (depressedC810 h (octicDepressionR810 h a7) a7
                    a6 a5 a4)
                  (depressedP810 h (octicDepressionR810 h a7) b9
                    b8)
                  (depressedR810 h (octicDepressionR810 h a7) b9
                    b8 b7 b6)) *
              ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7
                  a6) := by
      ring
    rw [hscale, h2048gamma, h16A]
  have hdiff :
      (131072 : F) * h ^ 42 *
          epsilonResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
              a4)
            (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3)
            (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 a2)
            (depressedP810 h (octicDepressionR810 h a7) b9 b8)
            (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
            (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7
              b6)
            (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6
              b5 b4) =
        (131072 : F) * h ^ 42 *
            depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6
              b5 b4 -
          (163840 : F) * h ^ 42 *
            depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 a2 +
          (36864 : F) * lambda * h ^ 42 *
            depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 +
          (4608 : F) * lambda * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5) +
          (5120 : F) * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 3 -
          (40960 : F) * h ^ 42 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4) -
          (20480 : F) * h ^ 42 *
            (depressedB810 h (octicDepressionR810 h a7) a7 a6
              a5) ^ 2 -
          (131072 : F) * h ^ 42 *
            (alphaResidual810
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedP810 h (octicDepressionR810 h a7) b9
                  b8) *
              depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4) -
          (114688 : F) * h ^ 42 *
            (betaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                  b7) *
              depressedB810 h (octicDepressionR810 h a7) a7 a6
                a5) -
          (98304 : F) * h ^ 42 *
            (gammaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedC810 h (octicDepressionR810 h a7) a7 a6
                  a5 a4)
                (depressedP810 h (octicDepressionR810 h a7) b9
                  b8)
                (depressedR810 h (octicDepressionR810 h a7) b9 b8
                  b7 b6) *
              depressedA810 h (octicDepressionR810 h a7) a7
                a6) := by
    simp only [epsilonResidual810, alphaResidual810, betaResidual810,
      gammaResidual810, hL]
    field_simp [h4, h8, h16, h32, h64, h128]
    ring
  rw [hdiff, h131072T, h163840E, h36864D, h4608AB, h5120A3, h40960AC,
    h20480B2, h131072alphaC, h114688betaB, h98304gammaA]
  ring

end Depression810Sixth

/-! ## Degree-`11` depressed Jacobian coefficient -/

section DepressedRow810Sixth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`11` Jacobian coefficient is
exactly `10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 4 C P' - 5 B Q' - 6 A R' - 8 T'`. -/
theorem differentialJacobian_coeff_11_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 11 =
      (10 : F) * d (f.coeff 2) + (9 : F) * g.coeff 9 * d (f.coeff 3) +
        (8 : F) * g.coeff 8 * d (f.coeff 4) +
        (7 : F) * g.coeff 7 * d (f.coeff 5) +
        (6 : F) * g.coeff 6 * d (f.coeff 6) -
          (4 : F) * f.coeff 4 * d (g.coeff 8) -
          (5 : F) * f.coeff 5 * d (g.coeff 7) -
          (6 : F) * f.coeff 6 * d (g.coeff 6) -
          (8 : F) * d (g.coeff 4) := by
  have hfd_high : ∀ n, 7 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf7]
    · have : 8 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq8 | hlt8
      · subst n
        simpa [hf8, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 8 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 8 < n + 1 := by omega
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
  have hmem65 : ((6, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem74 : ((7, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 11 =
        (10 : F) * d (f.coeff 2) +
          (9 : F) * g.coeff 9 * d (f.coeff 3) +
          (8 : F) * g.coeff 8 * d (f.coeff 4) +
          (7 : F) * g.coeff 7 * d (f.coeff 5) +
          (6 : F) * g.coeff 6 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne29_38 : ((2, 9) : ℕ × ℕ) ≠ (3, 8) := by decide
    have hne29_47 : ((2, 9) : ℕ × ℕ) ≠ (4, 7) := by decide
    have hne29_56 : ((2, 9) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hne29_65 : ((2, 9) : ℕ × ℕ) ≠ (6, 5) := by decide
    have hne38_47 : ((3, 8) : ℕ × ℕ) ≠ (4, 7) := by decide
    have hne38_56 : ((3, 8) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hne38_65 : ((3, 8) : ℕ × ℕ) ≠ (6, 5) := by decide
    have hne47_56 : ((4, 7) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hne47_65 : ((4, 7) : ℕ × ℕ) ≠ (6, 5) := by decide
    have hne56_65 : ((5, 6) : ℕ × ℕ) ≠ (6, 5) := by decide
    have hsubset :
        ({(2, 9), (3, 8), (4, 7), (5, 6), (6, 5)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (11 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem29
      · subst b; exact hmem38
      · subst b; exact hmem47
      · subst b; exact hmem56
      · subst b; exact hmem65
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(2, 9), (3, 8), (4, 7), (5, 6), (6, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne29 : b ≠ (2, 9) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne38 : b ≠ (3, 8) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne47 : b ≠ (4, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne56 : b ≠ (5, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne65 : b ≠ (6, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne2 : b.1 ≠ 2 := by
          intro h2; apply hne29; ext; exact h2; omega
        have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne38; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne47; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne56; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne65; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(2, 9), (3, 8), (4, 7), (5, 6), (6, 5)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 2 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 5 := by
      rw [Finset.sum_insert (by simp [hne29_38, hne29_47, hne29_56, hne29_65]),
        Finset.sum_insert (by simp [hne38_47, hne38_56, hne38_65]),
        Finset.sum_insert (by simp [hne47_56, hne47_65]),
        Finset.sum_insert (by simp [hne56_65]), Finset.sum_singleton]
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
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder9, hder8, hder7, hder6, hder5]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 11 =
        (4 : F) * f.coeff 4 * d (g.coeff 8) +
          (5 : F) * f.coeff 5 * d (g.coeff 7) +
          (6 : F) * f.coeff 6 * d (g.coeff 6) +
          (8 : F) * d (g.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne38_47 : ((3, 8) : ℕ × ℕ) ≠ (4, 7) := by decide
    have hne38_56 : ((3, 8) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hne38_74 : ((3, 8) : ℕ × ℕ) ≠ (7, 4) := by decide
    have hne47_56 : ((4, 7) : ℕ × ℕ) ≠ (5, 6) := by decide
    have hne47_74 : ((4, 7) : ℕ × ℕ) ≠ (7, 4) := by decide
    have hne56_74 : ((5, 6) : ℕ × ℕ) ≠ (7, 4) := by decide
    have hsubset : ({(3, 8), (4, 7), (5, 6), (7, 4)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (11 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem38
      · subst b; exact hmem47
      · subst b; exact hmem56
      · subst b; exact hmem74
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (11 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(3, 8), (4, 7), (5, 6), (7, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 11 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne38 : b ≠ (3, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne47 : b ≠ (4, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne56 : b ≠ (5, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne74 : b ≠ (7, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne3 : b.1 ≠ 3 := by
            intro h3; apply hne38; ext; exact h3; omega
          have hne4 : b.1 ≠ 4 := by
            intro h4; apply hne47; ext; exact h4; omega
          have hne5 : b.1 ≠ 5 := by
            intro h5; apply hne56; ext; exact h5; omega
          have hne7 : b.1 ≠ 7 := by
            intro h7; apply hne74; ext; exact h7; omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(3, 8), (4, 7), (5, 6), (7, 4)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 3 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 4 := by
      rw [Finset.sum_insert (by simp [hne38_47, hne38_56, hne38_74]),
        Finset.sum_insert (by simp [hne47_56, hne47_74]),
        Finset.sum_insert (by simp [hne56_74]), Finset.sum_singleton]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : f.derivative.coeff 4 = (5 : F) * f.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder3, hder4,
      hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem epsilonResidual810_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R T0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hrow : (10 : F) * d E0 + (9 : F) * L * d D0 +
        (8 : F) * P * d C0 + (7 : F) * Q * d B +
        (6 : F) * R * d A - (4 : F) * C0 * d P -
        (5 : F) * B * d Q - (6 : F) * A * d R -
        (8 : F) * d T0 = 0) :
    d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0 := by
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2 : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2]
    ring
  have hP0 : d P - (5 / 4 : F) * d A = 0 := by
    linear_combination hPderiv
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A) := by
    simp only [gammaResidual810, alphaResidual810, map_sub, map_add,
      Derivation.leibniz, h54, h98, h532, hL, zero_mul, add_zero,
      mul_zero, pow_two, hsq, hPderiv]
    ring
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (9 / 8 : F) * L * d D0 +
        (1 : F) * P * d C0 + (7 / 8 : F) * Q * d B +
        (3 / 4 : F) * R * d A - (1 / 2 : F) * C0 * d P -
        (5 / 8 : F) * B * d Q - (3 / 4 : F) * A * d R := by
    linear_combination (-1 / 8 : F) * hrow
  simp only [epsilonResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, map_sub, map_add, Derivation.leibniz, h54, h98,
    h78, h34, h532, h516, h5128, h964, hL, zero_mul, add_zero, mul_zero,
    pow_two, hsq, hsqB, hcub]
  rw [hTderiv, hPderiv, hQderiv, hRderiv]
  ring

end DepressedRow810Sixth

/-! ## Affine depression of a degree-ten source, `z⁴` coefficient -/

section AffineDecic810Sixth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁴` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff4_810
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

end AffineDecic810Sixth

/-! ## Local scalar identities at a simple root -/

section SixthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- The fifth-face jet reduces the third and sixth defects to a finite
scalar system in `(p₅, w₀)`.  That system forces both scalars to vanish. -/
theorem sixthFace_rootScalars_vanish810
    (a5 w : F)
    (hT : (512 : F) * w - (640 : F) * a5 = 0)
    (hW : (122880 : F) * a5 ^ 2 - (114688 : F) * a5 * w = 0) :
    a5 = 0 ∧ w = 0 := by
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hrel : (4 : F) * w - (5 : F) * a5 = 0 := by
    have hcomb : (128 : F) * ((4 : F) * w - (5 : F) * a5) = 0 := by
      linear_combination hT
    exact (mul_eq_zero.mp hcomb).resolve_left h128
  have hprod : a5 * ((122880 : F) * a5 - (114688 : F) * w) = 0 := by
    linear_combination hW
  rcases mul_eq_zero.mp hprod with ha0 | hface
  · have hw0 : w = 0 := by
      have h512 : (512 : F) ≠ 0 := by norm_num
      have : (512 : F) * w = 0 := by
        rw [ha0] at hT
        linear_combination hT
      exact (mul_eq_zero.mp this).resolve_left h512
    exact ⟨ha0, hw0⟩
  · have ht4 : -(81920 : F) * a5 = 0 := by
      linear_combination (4 : F) * hface + (114688 : F) * hrel
    have h81920 : (81920 : F) ≠ 0 := by norm_num
    have ha0 : a5 = 0 :=
      (mul_eq_zero.mp (by linear_combination -ht4)).resolve_left h81920
    have hw0 : w = 0 := by
      have h512 : (512 : F) ≠ 0 := by norm_num
      have : (512 : F) * w = 0 := by
        rw [ha0] at hT
        linear_combination hT
      exact (mul_eq_zero.mp this).resolve_left h512
    exact ⟨ha0, hw0⟩

/-- Parenthetical of the fifth-face jet in the cleared sixth defect. -/
def sixthJetParen810
    (h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F) : F[X] :=
  (122880 : F[X]) * a5 ^ 2 - (114688 : F[X]) * a5 * w0 +
    ((196608 : F[X]) * a5 * s0 * t0 -
        (337920 : F[X]) * a5 * t0 * v0 -
      (98304 : F[X]) * b6 * v0 + (98304 : F[X]) * s0 * v0 ^ 2 +
        (172032 : F[X]) * t0 * v0 * w0 -
      (102400 : F[X]) * v0 ^ 3) * h +
    (-(55296 : F[X]) * a5 * Polynomial.C lambda * v0 +
          (12800 : F[X]) * a5 * t0 ^ 3 +
        (73728 : F[X]) * b6 * t0 ^ 2 -
          (245760 : F[X]) * s0 * t0 ^ 2 * v0 -
        (71680 : F[X]) * t0 ^ 3 * w0 +
          (192000 : F[X]) * t0 ^ 2 * v0 ^ 2) * h ^ 2 +
    (-(131072 : F[X]) * a4 * s0 + (245760 : F[X]) * a4 * v0 +
          (69120 : F[X]) * a5 * Polynomial.C lambda * t0 ^ 2 +
        (69120 : F[X]) * Polynomial.C lambda * t0 * v0 ^ 2 +
          (71680 : F[X]) * s0 * t0 ^ 4) * h ^ 3 +
    (-(30720 : F[X]) * a4 * t0 ^ 2 - (81920 : F[X]) * b5 * t0 -
          (80640 : F[X]) * Polynomial.C lambda * t0 ^ 3 * v0 -
        (16800 : F[X]) * t0 ^ 6) * h ^ 4 +
    (-(55296 : F[X]) * a4 * Polynomial.C lambda * t0 +
          (18144 : F[X]) * Polynomial.C lambda * t0 ^ 5) * h ^ 5 +
    ((61440 : F[X]) * a3 * t0 + (131072 : F[X]) * b4) * h ^ 6 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda) * h ^ 7 +
    (-(163840 : F[X]) * a2) * h ^ 8

set_option maxHeartbeats 4000000 in
/-- The fifth-face jet factors the cleared sixth defect as `h³²` times a
polynomial whose constant term is the scalar system in `(p₅, w₀)`. -/
theorem localClearedSixthDefect810_of_fifthJet
    (h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F) :
    localClearedSixthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) a5 a4 a3 a2
        (h ^ 5 * s0) (h ^ 2 * w0) b6 b5 b4 lambda =
      h ^ 32 * sixthJetParen810 h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4
          lambda := by
  simp only [localClearedSixthDefect810, sixthJetParen810]
  ring

theorem localClearedThirdDefect810_of_fifthJet
    (h t0 v0 s0 w0 a5 : F[X]) (lambda : F) :
    localClearedThirdDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) a5
        (h ^ 5 * s0) (h ^ 2 * w0) lambda =
      h ^ 16 *
        ((512 : F[X]) * w0 - (640 : F[X]) * a5 +
          (-(512 : F[X]) * t0 * s0 + (480 : F[X]) * t0 * v0) * h +
          ((100 : F[X]) * t0 ^ 3 +
              (144 : F[X]) * Polynomial.C lambda * v0) * h ^ 2 -
            (135 : F[X]) * Polynomial.C lambda * t0 ^ 2 * h ^ 3) := by
  simp only [localClearedThirdDefect810]
  ring

theorem eval_localClearedThirdDefect810_fifthJet_paren
    (h t0 v0 s0 w0 a5 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        ((512 : F[X]) * w0 - (640 : F[X]) * a5 +
          (-(512 : F[X]) * t0 * s0 + (480 : F[X]) * t0 * v0) * h +
        ((100 : F[X]) * t0 ^ 3 +
            (144 : F[X]) * Polynomial.C lambda * v0) * h ^ 2 -
          (135 : F[X]) * Polynomial.C lambda * t0 ^ 2 * h ^ 3) =
      (512 : F) * Polynomial.eval root w0 -
        (640 : F) * Polynomial.eval root a5 := by
  simp [hroot]

theorem eval_localClearedSixthDefect810_fifthJet_paren
    (h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (sixthJetParen810 h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 lambda) =
      (122880 : F) * (Polynomial.eval root a5) ^ 2 -
        (114688 : F) * Polynomial.eval root a5 *
          Polynomial.eval root w0 := by
  simp [sixthJetParen810, hroot]

theorem sixthJetParen810_eval_of_power
    (h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 : F[X]) (lambda zeta : F)
    (root : F) (hroot : Polynomial.eval root h = 0)
    (hpow : sixthJetParen810 h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 lambda =
      Polynomial.C zeta * h ^ 10) :
    (122880 : F) * (Polynomial.eval root a5) ^ 2 -
      (114688 : F) * Polynomial.eval root a5 *
        Polynomial.eval root w0 = 0 := by
  have hleft := eval_localClearedSixthDefect810_fifthJet_paren h t0 v0 s0
    w0 a5 a4 a3 a2 b6 b5 b4 lambda root hroot
  have hzero :
      Polynomial.eval root
          (sixthJetParen810 h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 lambda) =
        0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

/-- Fifth-jet parenthetical of the cleared third defect. -/
def thirdJetParen810
    (h t0 v0 s0 w0 a5 : F[X]) (lambda : F) : F[X] :=
  (512 : F[X]) * w0 - (640 : F[X]) * a5 +
    (-(512 : F[X]) * t0 * s0 + (480 : F[X]) * t0 * v0) * h +
    ((100 : F[X]) * t0 ^ 3 +
        (144 : F[X]) * Polynomial.C lambda * v0) * h ^ 2 -
      (135 : F[X]) * Polynomial.C lambda * t0 ^ 2 * h ^ 3

theorem localClearedThirdDefect810_of_fifthJet_paren
    (h t0 v0 s0 w0 a5 : F[X]) (lambda : F) :
    localClearedThirdDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) a5
        (h ^ 5 * s0) (h ^ 2 * w0) lambda =
      h ^ 16 * thirdJetParen810 h t0 v0 s0 w0 a5 lambda := by
  simp only [localClearedThirdDefect810, thirdJetParen810]
  ring

theorem thirdJetParen810_eq_of_power
    (h t0 v0 s0 w0 a5 : F[X]) (lambda gamma : F) (hh : h ≠ 0)
    (hT : localClearedThirdDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) a5
        (h ^ 5 * s0) (h ^ 2 * w0) lambda =
      Polynomial.C gamma * h ^ 21) :
    thirdJetParen810 h t0 v0 s0 w0 a5 lambda =
      Polynomial.C gamma * h ^ 5 := by
  have hfactor :=
    localClearedThirdDefect810_of_fifthJet_paren h t0 v0 s0 w0 a5 lambda
  have hscale : Polynomial.C gamma * h ^ 21 =
      h ^ 16 * (Polynomial.C gamma * h ^ 5) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 16 hh)
  rw [← hfactor, hT, hscale]

theorem sixthJetParen810_eq_of_power
    (h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 : F[X]) (lambda zeta : F)
    (hh : h ≠ 0)
    (hW : localClearedSixthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) a5 a4
        a3 a2 (h ^ 5 * s0) (h ^ 2 * w0) b6 b5 b4 lambda =
      Polynomial.C zeta * h ^ 42) :
    sixthJetParen810 h t0 v0 s0 w0 a5 a4 a3 a2 b6 b5 b4 lambda =
      Polynomial.C zeta * h ^ 10 := by
  have hfactor := localClearedSixthDefect810_of_fifthJet h t0 v0 s0 w0
    a5 a4 a3 a2 b6 b5 b4 lambda
  have hscale : Polynomial.C zeta * h ^ 42 =
      h ^ 32 * (Polynomial.C zeta * h ^ 10) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 32 hh)
  rw [← hfactor, hW, hscale]

theorem eval_thirdJetParen810
    (h t0 v0 s0 w0 a5 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root (thirdJetParen810 h t0 v0 s0 w0 a5 lambda) =
      (512 : F) * Polynomial.eval root w0 -
        (640 : F) * Polynomial.eval root a5 := by
  simp [thirdJetParen810, hroot]

theorem thirdJetParen810_eval_of_power
    (h t0 v0 s0 w0 a5 : F[X]) (lambda gamma : F)
    (root : F) (hroot : Polynomial.eval root h = 0)
    (hpow : thirdJetParen810 h t0 v0 s0 w0 a5 lambda =
      Polynomial.C gamma * h ^ 5) :
    (512 : F) * Polynomial.eval root w0 -
      (640 : F) * Polynomial.eval root a5 = 0 := by
  have hleft := eval_thirdJetParen810 h t0 v0 s0 w0 a5 lambda root hroot
  have hzero :
      Polynomial.eval root (thirdJetParen810 h t0 v0 s0 w0 a5 lambda) =
        0 := by
    rw [hpow]
    simp [hroot]
  rw [← hleft]
  exact hzero

theorem sixthFace_q7_order_three810
    (h w0 q7 : F[X]) (hw0 : q7 = h ^ 2 * w0) (hdvd : h ∣ w0) :
    h ^ 3 ∣ q7 := by
  obtain ⟨w1, hw1⟩ := hdvd
  refine ⟨w1, ?_⟩
  rw [hw0, hw1]
  ring

end SixthFaceScalars810

/-! ## Source-facing sixth-face packet -/

section NonzeroSixthFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The fifth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁴²`. -/
theorem nonzeroFace810_sixthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ zeta : k,
      localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 42 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = h ^ 8 := by
    simp only [hp8, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = h ^ 10 := by
    simp only [hq10, hH, h, map_pow]
    ring
  have hpDep := affineDepress_sourceOctic68 p h
    (octicDepressionR810 h a7) hp hh hpTop
  have hL0 : depressedL68 h (octicDepressionR810 h a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter h a7 hh
  have hNrat : 5 * a7 * h ^ 2 - 4 * b9 = RatFunc.C lambda * h ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 h (octicDepressionR810 h a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower h a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h (octicDepressionR810 h a7) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 h (octicDepressionR810 h a7) (sourceToRatFunc68 q)
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = h ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedQ810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedR810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg8' :
      g.coeff 8 =
        depressedP810 h (octicDepressionR810 h a7) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * octicDepressionR810 h a7 +
        (sourceToRatFunc68 q).coeff 9 / h ^ 9 =
          depressedL810 h (octicDepressionR810 h a7) b9 := by
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow15 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_15_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 15) hbracket
    simpa [f, g, Polynomial.coeff_C, show (15 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow14 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 5) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 6) -
        (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_14_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 14) hbracket
    simpa [f, g, Polynomial.coeff_C, show (14 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 5) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 8) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 5) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 6) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf6 : f.coeff 6 = depressedA810 h (octicDepressionR810 h a7) a7 a6 := by
    dsimp only [f, depressedA810, a7, a6]
    rw [hpDep, coeff_depressedOctic68_six]
  have hf5 : f.coeff 5 =
      depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 := by
    dsimp only [f, depressedB810, a7, a6, a5]
    rw [hpDep, coeff_depressedOctic68_five]
  have hf4 : f.coeff 4 =
      depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 := by
    dsimp only [f, depressedC810, a7, a6, a5, a4]
    rw [hpDep, coeff_depressedOctic68_four]
  have hf3 : f.coeff 3 =
      depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 := by
    dsimp only [f, depressedD810, a7, a6, a5, a4, a3]
    rw [hpDep, coeff_depressedOctic68_three]
  have hf2 : f.coeff 2 =
      depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 := by
    dsimp only [f, depressedE810, a7, a6, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedOctic68_two]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual810 (f.coeff 6) (g.coeff 8)) = 0 :=
    alphaResidual810_deriv_zero ratFuncDerivation68 (f.coeff 6)
      (g.coeff 8) hrow15
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (g.coeff 7)) = 0 :=
    betaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (g.coeff 7) hLconst (by simpa using hrow14)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow13)
  have hepsilon0deriv :
      ratFuncDerivation68
        (epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow11)
  obtain ⟨zeta0, hzeta0⟩ :
      ∃ a : k,
        epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 4) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hepsilon0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda) =
        (131072 : RatFunc k) * h ^ 42 *
          epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 4) := by
    have hF := sixthDefect_eq_clearedEpsilon810 h a7 a6 a5 a4 a3 a2 b9
      b8 b7 b6 b5 b4 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedSixthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, h, a7, a6, a5, a4, a3, a2,
      b8, b7, b6, b5, b4, epsilonResidual810, alphaResidual810,
      betaResidual810, gammaResidual810, hf6, hf5, hf4, hf3, hf2, hg4,
      hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (131072 * zeta0) * h0 ^ 42) := by
    rw [hclear, hzeta0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨131072 * zeta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Finite local initial packet: the degree-one scale divides the
subleading octic coefficient to order six, the next octic coefficient
to order three, `p₅` to order one, the first unused decic coefficient
to order five, `q₇` to order three, and `q₉` to order eight. -/
theorem nonzeroFace810_linearRoot_sixthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    h0 ^ 6 ∣ p.coeff 7 ∧ h0 ^ 3 ∣ p.coeff 6 ∧ h0 ∣ p.coeff 5 ∧
      h0 ^ 5 ∣ q.coeff 8 ∧ h0 ^ 3 ∣ q.coeff 7 ∧ h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨gamma0, hT⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨hp7d, hp6d, hq8d, hq7d, hq9d⟩ :=
    nonzeroFace810_linearRoot_fifthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ⟨t0, ht0⟩ := hp7d
  have ⟨v0, hv0⟩ := hp6d
  have ⟨s0, hs0⟩ := hq8d
  have ⟨w0, hw0⟩ := hq7d
  have hTsubst :
      localClearedThirdDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (p.coeff 5) (h0 ^ 5 * s0) (h0 ^ 2 * w0) lambda =
        localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
    simp only [ht0, hv0, hs0, hw0]
  have hWsubst :
      localClearedSixthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (h0 ^ 5 * s0) (h0 ^ 2 * w0) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) lambda =
        localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) lambda := by
    simp only [ht0, hv0, hs0, hw0]
  have hTparen :
      thirdJetParen810 h0 t0 v0 s0 w0 (p.coeff 5) lambda =
        Polynomial.C gamma0 * h0 ^ 5 :=
    thirdJetParen810_eq_of_power h0 t0 v0 s0 w0 (p.coeff 5) lambda
      gamma0 hh0 (hTsubst.trans hT)
  have hWparen :
      sixthJetParen810 h0 t0 v0 s0 w0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 10 :=
    sixthJetParen810_eq_of_power h0 t0 v0 s0 w0 (p.coeff 5)
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5)
      (q.coeff 4) lambda zeta hh0 (hWsubst.trans hWrel)
  have hTroot :=
    thirdJetParen810_eval_of_power h0 t0 v0 s0 w0 (p.coeff 5) lambda
      gamma0 a hroot hTparen
  have hWroot :=
    sixthJetParen810_eval_of_power h0 t0 v0 s0 w0 (p.coeff 5)
      (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5)
      (q.coeff 4) lambda zeta a hroot hWparen
  obtain ⟨ha50, hw00⟩ :=
    sixthFace_rootScalars_vanish810 (Polynomial.eval a (p.coeff 5))
      (Polynomial.eval a w0) hTroot hWroot
  have hp5_div : h0 ∣ p.coeff 5 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 5) a hh0degree
      hroot ha50
  have hw0_div : h0 ∣ w0 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w0 a hh0degree hroot hw00
  exact ⟨hp7d, hp6d, hp5_div, hq8d,
    sixthFace_q7_order_three810 h0 w0 (q.coeff 7) hw0 hw0_div, hq9d⟩

/-- Source-facing sixth integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_sixthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda zeta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) lambda =
          Polynomial.C zeta * h0 ^ 42 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, _hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, zeta, hh0, hlambda, hh0degree, hH, hN', hWrel⟩

/-- Finite local initial packet of a normalized scale-two `(8,10)`
nonzero face: the degree-one scale divides `p₇` to order six, `p₆` to
order three, `p₅` to order one, `q₈` to order five, `q₇` to order
three, and `q₉` to order eight. -/
theorem normalized810ScaleTwo_nonzeroFace_sixthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        h0 ^ 6 ∣ p.coeff 7 ∧ h0 ^ 3 ∣ p.coeff 6 ∧ h0 ∣ p.coeff 5 ∧
        h0 ^ 5 ∣ q.coeff 8 ∧ h0 ^ 3 ∣ q.coeff 7 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨hp7, hp6, hp5, hq8, hq7, hq9⟩ :=
    nonzeroFace810_linearRoot_sixthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp7, hp6, hp5,
    hq8, hq7, hq9, hN'⟩

end NonzeroSixthFace810

#print axioms sixthCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_11_monicOcticDecic
#print axioms sixthDefect_eq_clearedEpsilon810
#print axioms epsilonResidual810_deriv_zero
#print axioms localClearedSixthDefect810_of_fifthJet
#print axioms localClearedThirdDefect810_of_fifthJet
#print axioms sixthFace_rootScalars_vanish810
#print axioms sixthJetParen810_eval_of_power
#print axioms thirdJetParen810_eq_of_power
#print axioms sixthJetParen810_eq_of_power
#print axioms thirdJetParen810_eval_of_power
#print axioms sixthFace_q7_order_three810
#print axioms nonzeroFace810_sixthDefectPowerRelation
#print axioms nonzeroFace810_linearRoot_sixthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_sixthDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_sixthInitialPacket

end Max11DegreeRoutes
