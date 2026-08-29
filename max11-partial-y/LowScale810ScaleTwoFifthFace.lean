import LowScale810ScaleTwoFourthFace

/-! # Scale-two fifth face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the fourth face supplies the degree-`13` integral
and the local jet `h⁵ ∣ p₇`, `h² ∣ p₆`, `h⁴ ∣ q₈`, `h ∣ q₇`,
`h⁷ ∣ q₉`.  The next Keller coefficient is the degree-`12` Jacobian
row.  After the same octic depression that kills `z⁷`, that row is
`10 D' + 9 L C' + 8 P B' + 7 Q A' - 5 B P' - 6 A Q' - 8 S' = 0`.
The resulting first integral clears to a polynomial defect `V` of
weight thirty-five.

Evaluating the second, third, fourth, and fifth defects together at
the root of `h` forces the finite initial jet `h⁶ ∣ p₇`, `h³ ∣ p₆`,
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
degrees `(8,10)`.  It is the source of the first mixed octic/decic
`z³`/`z⁵` defect after the degree-`13` integral. -/
theorem fifthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 7).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 5).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 6).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 10).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 12) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1),
        (12, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC8, hC9, hC10, hC7, hC6, hC5, hC4, hC3]
  linear_combination hcoeff

/-! ## Octic `z³` and decic `z⁵` coordinates -/

section Depression810Fifth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z³` coefficient. -/
def depressedD810 (h r a7 a6 a5 a4 a3 : F) : F :=
  depressedS68 h r a7 a6 a5 a4 a3

/-- Depressed decic `z⁵` coefficient. -/
def depressedS810 (h r b9 b8 b7 b6 b5 : F) : F :=
  -252 * r ^ 5 + 126 * (b9 / h ^ 9) * r ^ 4 -
    56 * (b8 / h ^ 8) * r ^ 3 + 21 * (b7 / h ^ 7) * r ^ 2 -
    6 * (b6 / h ^ 6) * r + b5 / h ^ 5

/-- First residual of the degree-`12` row. -/
def deltaResidual810 (L A B C0 D0 P Q S0 : F) : F :=
  S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
    alphaResidual810 A P * B +
    (7 / 8 : F) * betaResidual810 L A B Q * A +
    (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)

/-- Polynomial numerator of `131072 h³⁵ δ` on the ninth-power face. -/
def localClearedFifthDefect810
    (h a7 a6 a5 a4 a3 b8 b7 b6 b5 : F[X]) (lambda : F) : F[X] :=
  -(163840 : F[X]) * a3 * h ^ 32 +
    (81920 : F[X]) * a4 * a7 * h ^ 24 +
    (36864 : F[X]) * Polynomial.C lambda * a4 * h ^ 31 +
    (266240 : F[X]) * a5 * a6 * h ^ 24 -
    (49920 : F[X]) * a5 * a7 ^ 2 * h ^ 16 -
    (59904 : F[X]) * Polynomial.C lambda * a5 * a7 * h ^ 23 -
    (131072 : F[X]) * a5 * b8 * h ^ 22 -
    (199680 : F[X]) * a6 ^ 2 * a7 * h ^ 16 -
    (29952 : F[X]) * Polynomial.C lambda * a6 ^ 2 * h ^ 23 +
    (29120 : F[X]) * a6 * a7 ^ 3 * h ^ 8 +
    (78624 : F[X]) * Polynomial.C lambda * a6 * a7 ^ 2 * h ^ 15 +
    (212992 : F[X]) * a6 * a7 * b8 * h ^ 14 -
    (114688 : F[X]) * a6 * b7 * h ^ 22 +
    (21112 : F[X]) * a7 ^ 5 -
    (23751 : F[X]) * Polynomial.C lambda * a7 ^ 4 * h ^ 7 -
    (93184 : F[X]) * a7 ^ 3 * b8 * h ^ 6 +
    (93184 : F[X]) * a7 ^ 2 * b7 * h ^ 14 -
    (98304 : F[X]) * a7 * b6 * h ^ 22 +
    (131072 : F[X]) * b5 * h ^ 30

theorem coeff_depressedOctic68_three
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 3 = S := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z³` coordinate. -/
theorem depressedD810_eq_cleared
    (h a7 a6 a5 a4 a3 : F) (hh : h ≠ 0) :
    depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
      (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
          160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
          7 * a7 ^ 5) /
        (1024 * h ^ 35) := by
  simp only [depressedD810, depressedS68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z⁵` coordinate on the
ninth-power face. -/
theorem depressedS810_eq_cleared
    (h a7 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
      (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
          896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
          6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
        (8192 * h ^ 35) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedS810, octicDepressionR810]
  have hrewrite :
      -252 * (a7 / (8 * h ^ 7)) ^ 5 +
          126 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 4 -
        56 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 3 +
          21 * (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) ^ 2 -
        6 * (b6 / h ^ 6) * (a7 / (8 * h ^ 7)) + b5 / h ^ 5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) := by
    field_simp [hh, h8, hh2, hh5, hh6, hh7, hh8pow, hh9, hh35, h8192]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      have h4 : (4 : F) ≠ 0 := by norm_num
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, hh2, hh5, hh6, hh7, hh8pow, hh9, hh35, h8192]
    ring
  exact hrewrite

set_option maxHeartbeats 8000000 in
/-- Clearing the first integral
`S - (5/4) D - (9/8) L C - α B - (7/8) β A - (5/16) A B - (9/128) L A²`
against `h³⁵` on the ninth-power face. -/
theorem fifthDefect_eq_clearedDelta810
    (h a7 a6 a5 a4 a3 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (131072 : F) * h ^ 35 *
        deltaResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5) =
      -(163840 : F) * a3 * h ^ 32 + (81920 : F) * a4 * a7 * h ^ 24 +
        (36864 : F) * lambda * a4 * h ^ 31 +
        (266240 : F) * a5 * a6 * h ^ 24 -
        (49920 : F) * a5 * a7 ^ 2 * h ^ 16 -
        (59904 : F) * lambda * a5 * a7 * h ^ 23 -
        (131072 : F) * a5 * b8 * h ^ 22 -
        (199680 : F) * a6 ^ 2 * a7 * h ^ 16 -
        (29952 : F) * lambda * a6 ^ 2 * h ^ 23 +
        (29120 : F) * a6 * a7 ^ 3 * h ^ 8 +
        (78624 : F) * lambda * a6 * a7 ^ 2 * h ^ 15 +
        (212992 : F) * a6 * a7 * b8 * h ^ 14 -
        (114688 : F) * a6 * b7 * h ^ 22 + (21112 : F) * a7 ^ 5 -
        (23751 : F) * lambda * a7 ^ 4 * h ^ 7 -
        (93184 : F) * a7 ^ 3 * b8 * h ^ 6 +
        (93184 : F) * a7 ^ 2 * b7 * h ^ 14 -
        (98304 : F) * a7 * b6 * h ^ 22 +
        (131072 : F) * b5 * h ^ 30 := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
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
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
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
  have h8192S :
      (8192 : F) * h ^ 35 *
          depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 : F) * a7 ^ 5 - (63 : F) * lambda * a7 ^ 4 * h ^ 7 -
          (896 : F) * a7 ^ 3 * b8 * h ^ 6 +
          (2688 : F) * a7 ^ 2 * b7 * h ^ 14 -
          (6144 : F) * a7 * b6 * h ^ 22 +
          (8192 : F) * b5 * h ^ 30 := by
    rw [hS]
    field_simp [hh, h8192, hh35]
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
  have h131072S :
      (131072 : F) * h ^ 35 *
          depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (4032 : F) * a7 ^ 5 - (1008 : F) * lambda * a7 ^ 4 * h ^ 7 -
          (14336 : F) * a7 ^ 3 * b8 * h ^ 6 +
          (43008 : F) * a7 ^ 2 * b7 * h ^ 14 -
          (98304 : F) * a7 * b6 * h ^ 22 +
          (131072 : F) * b5 * h ^ 30 := by
    have hscale :
        (131072 : F) * h ^ 35 *
            depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6
              b5 =
          (16 : F) *
            ((8192 : F) * h ^ 35 *
              depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6
                b5) := by
      ring
    rw [hscale, h8192S]
    ring
  have h163840D :
      (163840 : F) * h ^ 35 *
          depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
        (163840 : F) * a3 * h ^ 32 - (81920 : F) * a4 * a7 * h ^ 24 +
          (25600 : F) * a5 * a7 ^ 2 * h ^ 16 -
          (6400 : F) * a6 * a7 ^ 3 * h ^ 8 + (1120 : F) * a7 ^ 5 := by
    have hscale :
        (163840 : F) * h ^ 35 *
            depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 =
          (160 : F) *
            ((1024 : F) * h ^ 35 *
              depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
                a3) := by
      ring
    rw [hscale, h1024D]
    ring
  have h36864C :
      (36864 : F) * lambda * h ^ 35 *
          depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
        (36864 : F) * lambda * a4 * h ^ 31 -
          (23040 : F) * lambda * a5 * a7 * h ^ 23 +
          (8640 : F) * lambda * a6 * a7 ^ 2 * h ^ 15 -
          (1890 : F) * lambda * a7 ^ 4 * h ^ 7 := by
    have hscale :
        (36864 : F) * lambda * h ^ 35 *
            depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
          (18 : F) * lambda * h ^ 7 *
            ((2048 : F) * h ^ 28 *
              depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
                a4) := by
      ring
    rw [hscale, h2048C]
    ring
  have h131072alphaB :
      (131072 : F) * h ^ 35 *
          (alphaResidual810
              (depressedA810 h (octicDepressionR810 h a7) a7 a6)
              (depressedP810 h (octicDepressionR810 h a7) b9 b8) *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
        (128 : F) *
          ((32 : F) * b8 * h ^ 6 - (40 : F) * a6 * h ^ 8 +
              (9 : F) * lambda * a7 * h ^ 7 - (5 : F) * a7 ^ 2) *
            ((32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
              (7 : F) * a7 ^ 3) := by
    have hscale :
        (131072 : F) * h ^ 35 *
            (alphaResidual810
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedP810 h (octicDepressionR810 h a7) b9 b8) *
              depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
          (128 : F) *
            ((32 : F) * h ^ 14 *
                alphaResidual810
                  (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                  (depressedP810 h (octicDepressionR810 h a7) b9
                    b8)) *
              ((32 : F) * h ^ 21 *
                depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5) := by
      ring
    rw [hscale, h32alpha, h32B]
  have h114688betaA :
      (114688 : F) * h ^ 35 *
          (betaResidual810
              (depressedL810 h (octicDepressionR810 h a7) b9)
              (depressedA810 h (octicDepressionR810 h a7) a7 a6)
              (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
              (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7) *
            depressedA810 h (octicDepressionR810 h a7) a7 a6) =
        (14 : F) *
          ((100 : F) * a7 ^ 3 - (512 : F) * a7 * b8 * h ^ 6 -
              (135 : F) * lambda * a7 ^ 2 * h ^ 7 +
              (480 : F) * a6 * a7 * h ^ 8 + (512 : F) * b7 * h ^ 14 +
              (144 : F) * lambda * a6 * h ^ 15 -
              (640 : F) * a5 * h ^ 16) *
            ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) := by
    have hscale :
        (114688 : F) * h ^ 35 *
            (betaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                  b7) *
              depressedA810 h (octicDepressionR810 h a7) a7 a6) =
          (14 : F) *
            ((512 : F) * h ^ 21 *
                betaResidual810
                  (depressedL810 h (octicDepressionR810 h a7) b9)
                  (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                  (depressedB810 h (octicDepressionR810 h a7) a7 a6
                    a5)
                  (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                    b7)) *
              ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7
                  a6) := by
      ring
    rw [hscale, h512beta, h16A]
  have h40960AB :
      (40960 : F) * h ^ 35 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
            depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
        (80 : F) *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) *
            ((32 : F) * a5 * h ^ 16 - (24 : F) * a6 * a7 * h ^ 8 +
              (7 : F) * a7 ^ 3) := by
    have hscale :
        (40960 : F) * h ^ 35 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) =
          (80 : F) *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7 a6) *
              ((32 : F) * h ^ 21 *
                depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5) := by
      ring
    rw [hscale, h16A, h32B]
  have h2304A2 :
      (2304 : F) * lambda * h ^ 35 *
          (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 =
        (9 : F) * lambda * h ^ 7 *
          ((16 : F) * a6 * h ^ 8 - (7 : F) * a7 ^ 2) ^ 2 := by
    have hscale :
        (2304 : F) * lambda * h ^ 35 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 =
          (9 : F) * lambda * h ^ 7 *
            ((16 : F) * h ^ 14 *
                depressedA810 h (octicDepressionR810 h a7) a7
                  a6) ^ 2 := by
      field_simp [hh, h16, hh14, hh35]
      ring
    rw [hscale, h16A]
  have hdiff :
      (131072 : F) * h ^ 35 *
          deltaResidual810
            (depressedL810 h (octicDepressionR810 h a7) b9)
            (depressedA810 h (octicDepressionR810 h a7) a7 a6)
            (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
            (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
            (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3)
            (depressedP810 h (octicDepressionR810 h a7) b9 b8)
            (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
            (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6
              b5) =
        (131072 : F) * h ^ 35 *
            depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6
              b5 -
          (163840 : F) * h ^ 35 *
            depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4
              a3 +
          (36864 : F) * lambda * h ^ 35 *
            depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 -
          (131072 : F) * h ^ 35 *
            (alphaResidual810
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedP810 h (octicDepressionR810 h a7) b9 b8) *
              depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) -
          (114688 : F) * h ^ 35 *
            (betaResidual810
                (depressedL810 h (octicDepressionR810 h a7) b9)
                (depressedA810 h (octicDepressionR810 h a7) a7 a6)
                (depressedB810 h (octicDepressionR810 h a7) a7 a6
                  a5)
                (depressedQ810 h (octicDepressionR810 h a7) b9 b8
                  b7) *
              depressedA810 h (octicDepressionR810 h a7) a7 a6) -
          (40960 : F) * h ^ 35 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6 *
              depressedB810 h (octicDepressionR810 h a7) a7 a6 a5) +
          (2304 : F) * lambda * h ^ 35 *
            (depressedA810 h (octicDepressionR810 h a7) a7 a6) ^ 2 :=
    by
    simp only [deltaResidual810, hL]
    field_simp [h4, h8, h16]
    ring
  rw [hdiff, h131072S, h163840D, h36864C, h131072alphaB, h114688betaA,
    h40960AB, h2304A2]
  ring

end Depression810Fifth

/-! ## Degree-`12` depressed Jacobian coefficient -/

section DepressedRow810Fifth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`12` Jacobian coefficient is
exactly `10 D' + 9 L C' + 8 P B' + 7 Q A' - 5 B P' - 6 A Q' - 8 S'`. -/
theorem differentialJacobian_coeff_12_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 12 =
      (10 : F) * d (f.coeff 3) + (9 : F) * g.coeff 9 * d (f.coeff 4) +
        (8 : F) * g.coeff 8 * d (f.coeff 5) +
        (7 : F) * g.coeff 7 * d (f.coeff 6) -
          (5 : F) * f.coeff 5 * d (g.coeff 8) -
          (6 : F) * f.coeff 6 * d (g.coeff 7) -
          (8 : F) * d (g.coeff 5) := by
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
  have hmem39 : ((3, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem48 : ((4, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem57 : ((5, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem66 : ((6, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem75 : ((7, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 12 =
        (10 : F) * d (f.coeff 3) +
          (9 : F) * g.coeff 9 * d (f.coeff 4) +
          (8 : F) * g.coeff 8 * d (f.coeff 5) +
          (7 : F) * g.coeff 7 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne39_48 : ((3, 9) : ℕ × ℕ) ≠ (4, 8) := by decide
    have hne39_57 : ((3, 9) : ℕ × ℕ) ≠ (5, 7) := by decide
    have hne39_66 : ((3, 9) : ℕ × ℕ) ≠ (6, 6) := by decide
    have hne48_57 : ((4, 8) : ℕ × ℕ) ≠ (5, 7) := by decide
    have hne48_66 : ((4, 8) : ℕ × ℕ) ≠ (6, 6) := by decide
    have hne57_66 : ((5, 7) : ℕ × ℕ) ≠ (6, 6) := by decide
    have hsubset : ({(3, 9), (4, 8), (5, 7), (6, 6)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (12 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb
      · subst b; exact hmem39
      · subst b; exact hmem48
      · subst b; exact hmem57
      · subst b; exact hmem66
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(3, 9), (4, 8), (5, 7), (6, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 12 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne39 : b ≠ (3, 9) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne48 : b ≠ (4, 8) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne57 : b ≠ (5, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne66 : b ≠ (6, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne39; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne48; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne57; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne66; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(3, 9), (4, 8), (5, 7), (6, 6)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 3 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 6 := by
      rw [Finset.sum_insert (by simp [hne39_48, hne39_57, hne39_66]),
        Finset.sum_insert (by simp [hne48_57, hne48_66]),
        Finset.sum_insert (by simp [hne57_66]), Finset.sum_singleton]
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
      (f.derivative * coefficientDeriv d g).coeff 12 =
        (5 : F) * f.coeff 5 * d (g.coeff 8) +
          (6 : F) * f.coeff 6 * d (g.coeff 7) +
          (8 : F) * d (g.coeff 5) := by
    rw [Polynomial.coeff_mul]
    have hne48_57 : ((4, 8) : ℕ × ℕ) ≠ (5, 7) := by decide
    have hne48_75 : ((4, 8) : ℕ × ℕ) ≠ (7, 5) := by decide
    have hne57_75 : ((5, 7) : ℕ × ℕ) ≠ (7, 5) := by decide
    have hsubset : ({(4, 8), (5, 7), (7, 5)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (12 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb
      · subst b; exact hmem48
      · subst b; exact hmem57
      · subst b; exact hmem75
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (12 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(4, 8), (5, 7), (7, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 12 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne48 : b ≠ (4, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne57 : b ≠ (5, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne75 : b ≠ (7, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne4 : b.1 ≠ 4 := by
            intro h4; apply hne48; ext; exact h4; omega
          have hne5 : b.1 ≠ 5 := by
            intro h5; apply hne57; ext; exact h5; omega
          have hne7 : b.1 ≠ 7 := by
            intro h7; apply hne75; ext; exact h7; omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(4, 8), (5, 7), (7, 5)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 4 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 5 := by
      rw [Finset.sum_insert (by simp [hne48_57, hne48_75]),
        Finset.sum_insert (by simp [hne57_75]), Finset.sum_singleton]
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
      coeff_coefficientDeriv, hder4, hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem deltaResidual810_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 P Q S0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hrow : (10 : F) * d D0 + (9 : F) * L * d C0 +
        (8 : F) * P * d B + (7 : F) * Q * d A -
        (5 : F) * B * d P - (6 : F) * A * d Q -
        (8 : F) * d S0 = 0) :
    d (deltaResidual810 L A B C0 D0 P Q S0) = 0 := by
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have hP0 : d P - (5 / 4 : F) * d A = 0 := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    exact halpha'
  have hQ0 : d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    exact hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        P * d B + (7 / 8 : F) * Q * d A - (5 / 8 : F) * B * d P -
        (3 / 4 : F) * A * d Q := by
    linear_combination (-1 / 8 : F) * hrow
  have hPderiv : d P = (5 / 4 : F) * d A := by
    linear_combination hP0
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    linear_combination hQ0
  simp only [deltaResidual810, alphaResidual810, betaResidual810, map_sub,
    map_add, Derivation.leibniz, h54, h98, h78, h516, h9128, hL, zero_mul,
    add_zero, mul_zero, pow_two, hsq]
  rw [hSderiv, hPderiv, hQderiv]
  ring

end DepressedRow810Fifth

/-! ## Affine depression of a degree-ten source, `z⁵` coefficient -/

section AffineDecic810Fifth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁵` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff5_810
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

end AffineDecic810Fifth

/-! ## Local scalar identities at a simple root -/

section FifthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- The fourth-face jet reduces `M`, `T`, `U`, and `V` to a finite scalar
system in `(t₁, v₂, s₂, w₁)`.  That system forces all four scalars to
vanish. -/
theorem fifthFace_rootScalars_vanish810
    (t1 v2 s2 w1 : F)
    (hM : (32 : F) * s2 - (40 : F) * v2 - (5 : F) * t1 ^ 2 = 0)
    (hT : (100 : F) * t1 ^ 3 - (512 : F) * t1 * s2 +
        (480 : F) * t1 * v2 + (512 : F) * w1 = 0)
    (hU : (1792 : F) * s2 * t1 ^ 2 - (2048 : F) * s2 * v2 -
        (385 : F) * t1 ^ 4 - (1120 : F) * t1 ^ 2 * v2 -
        (1792 : F) * t1 * w1 + (2240 : F) * v2 ^ 2 = 0)
    (hV : -(93184 : F) * s2 * t1 ^ 3 + (212992 : F) * s2 * t1 * v2 +
        (21112 : F) * t1 ^ 5 + (29120 : F) * t1 ^ 3 * v2 +
        (93184 : F) * t1 ^ 2 * w1 - (199680 : F) * t1 * v2 ^ 2 -
        (114688 : F) * v2 * w1 = 0) :
    t1 = 0 ∧ v2 = 0 ∧ s2 = 0 ∧ w1 = 0 := by
  have hidU :
      (2 : F) *
            ((1792 : F) * s2 * t1 ^ 2 - (2048 : F) * s2 * v2 -
              (385 : F) * t1 ^ 4 - (1120 : F) * t1 ^ 2 * v2 -
              (1792 : F) * t1 * w1 + (2240 : F) * v2 ^ 2) +
          (128 : F) * v2 *
            ((32 : F) * s2 - (40 : F) * v2 - (5 : F) * t1 ^ 2) +
          (7 : F) * t1 *
            ((100 : F) * t1 ^ 3 - (512 : F) * t1 * s2 +
              (480 : F) * t1 * v2 + (512 : F) * w1) =
        -(10 : F) * ((7 : F) * t1 ^ 4 - (48 : F) * t1 ^ 2 * v2 +
          (64 : F) * v2 ^ 2) := by
    ring
  have hidV :
      -(93184 : F) * s2 * t1 ^ 3 + (212992 : F) * s2 * t1 * v2 +
            (21112 : F) * t1 ^ 5 + (29120 : F) * t1 ^ 3 * v2 +
            (93184 : F) * t1 ^ 2 * w1 - (199680 : F) * t1 * v2 ^ 2 -
            (114688 : F) * v2 * w1 -
          (3072 : F) * t1 * v2 *
            ((32 : F) * s2 - (40 : F) * v2 - (5 : F) * t1 ^ 2) +
          (-(182 : F) * t1 ^ 2 + (224 : F) * v2) *
            ((100 : F) * t1 ^ 3 - (512 : F) * t1 * s2 +
              (480 : F) * t1 * v2 + (512 : F) * w1) =
        (32 : F) * t1 *
          ((91 : F) * t1 ^ 4 - (640 : F) * t1 ^ 2 * v2 +
            (960 : F) * v2 ^ 2) := by
    ring
  have hP : (7 : F) * t1 ^ 4 - (48 : F) * t1 ^ 2 * v2 +
      (64 : F) * v2 ^ 2 = 0 := by
    have h10 : (10 : F) ≠ 0 := by norm_num
    have hcomb :
        -(10 : F) * ((7 : F) * t1 ^ 4 - (48 : F) * t1 ^ 2 * v2 +
          (64 : F) * v2 ^ 2) = 0 := by
      rw [← hidU]
      linear_combination (2 : F) * hU + (128 : F) * v2 * hM +
        (7 : F) * t1 * hT
    exact (mul_eq_zero.mp (by linear_combination -hcomb)).resolve_left h10
  have hQprod : t1 *
      ((91 : F) * t1 ^ 4 - (640 : F) * t1 ^ 2 * v2 +
        (960 : F) * v2 ^ 2) = 0 := by
    have h32 : (32 : F) ≠ 0 := by norm_num
    have hcomb :
        (32 : F) *
          (t1 *
            ((91 : F) * t1 ^ 4 - (640 : F) * t1 ^ 2 * v2 +
              (960 : F) * v2 ^ 2)) = 0 := by
      have hraw :
          (32 : F) * t1 *
            ((91 : F) * t1 ^ 4 - (640 : F) * t1 ^ 2 * v2 +
              (960 : F) * v2 ^ 2) = 0 := by
        rw [← hidV]
        linear_combination hV - (3072 : F) * t1 * v2 * hM +
          (-(182 : F) * t1 ^ 2 + (224 : F) * v2) * hT
      linear_combination hraw
    exact (mul_eq_zero.mp hcomb).resolve_left h32
  have hidPQ :
      (15 : F) * ((7 : F) * t1 ^ 4 - (48 : F) * t1 ^ 2 * v2 +
            (64 : F) * v2 ^ 2) -
          ((91 : F) * t1 ^ 4 - (640 : F) * t1 ^ 2 * v2 +
            (960 : F) * v2 ^ 2) =
        (2 : F) * t1 ^ 2 * ((7 : F) * t1 ^ 2 - (40 : F) * v2) := by
    ring
  have hv_of_t0 (ht0 : t1 = 0) : v2 = 0 := by
    have hU0 : (64 : F) * v2 ^ 2 = 0 := by
      simpa [ht0] using hP
    have h64 : (64 : F) ≠ 0 := by norm_num
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hU0).resolve_left h64)
  have ht0v0 : t1 = 0 ∧ v2 = 0 := by
    rcases mul_eq_zero.mp hQprod with ht0 | hQ
    · exact ⟨ht0, hv_of_t0 ht0⟩
    · have hdiff :
          (2 : F) * t1 ^ 2 * ((7 : F) * t1 ^ 2 - (40 : F) * v2) = 0 := by
        rw [← hidPQ]
        linear_combination (15 : F) * hP - hQ
      have h2 : (2 : F) ≠ 0 := by norm_num
      have hprod : t1 ^ 2 * ((7 : F) * t1 ^ 2 - (40 : F) * v2) = 0 := by
        have hassoc :
            (2 : F) *
              (t1 ^ 2 * ((7 : F) * t1 ^ 2 - (40 : F) * v2)) = 0 := by
          linear_combination hdiff
        exact (mul_eq_zero.mp hassoc).resolve_left h2
      rcases mul_eq_zero.mp hprod with ht2 | hface
      · exact ⟨sq_eq_zero_iff.mp ht2, hv_of_t0 (sq_eq_zero_iff.mp ht2)⟩
      · have hidFace :
            (25 : F) * ((7 : F) * t1 ^ 4 - (48 : F) * t1 ^ 2 * v2 +
                  (64 : F) * v2 ^ 2) +
                (-(23 : F) * t1 ^ 2 + (40 : F) * v2) *
                  ((7 : F) * t1 ^ 2 - (40 : F) * v2) =
              (14 : F) * t1 ^ 4 := by
          ring
        have ht4 : (14 : F) * t1 ^ 4 = 0 := by
          rw [← hidFace]
          linear_combination (25 : F) * hP +
            (-(23 : F) * t1 ^ 2 + (40 : F) * v2) * hface
        have h14 : (14 : F) ≠ 0 := by norm_num
        have ht40 : t1 ^ 4 = 0 :=
          (mul_eq_zero.mp ht4).resolve_left h14
        have ht0 : t1 = 0 := by
          have hpow : t1 ^ 4 = (t1 ^ 2) ^ 2 := by ring
          have hsq : (t1 ^ 2) ^ 2 = 0 := by
            rw [← hpow]
            exact ht40
          exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hsq)
        exact ⟨ht0, hv_of_t0 ht0⟩
  have hs0 : s2 = 0 := by
    have h32 : (32 : F) ≠ 0 := by norm_num
    have : (32 : F) * s2 = 0 := by
      rw [ht0v0.1, ht0v0.2] at hM
      linear_combination hM
    exact (mul_eq_zero.mp this).resolve_left h32
  have hw0 : w1 = 0 := by
    have h512 : (512 : F) ≠ 0 := by norm_num
    have : (512 : F) * w1 = 0 := by
      rw [ht0v0.1, ht0v0.2] at hT
      linear_combination hT
    exact (mul_eq_zero.mp this).resolve_left h512
  exact ⟨ht0v0.1, ht0v0.2, hs0, hw0⟩

end FifthFaceScalars810

/-! ## Source-facing fifth-face packet -/

section NonzeroFifthFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The fourth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h³⁵`. -/
theorem nonzeroFace810_fifthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eps : k,
      localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) lambda =
        Polynomial.C eps * h0 ^ 35 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
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
  have hg5 :
      g.coeff 5 =
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedS810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
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
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 5) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 7) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
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
  have hdelta0deriv :
      ratFuncDerivation68
        (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow12)
  obtain ⟨eps0, heps0⟩ :
      ∃ a : k,
        deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
            (g.coeff 5) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hdelta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda) =
        (131072 : RatFunc k) * h ^ 35 *
          deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
            (g.coeff 5) := by
    have hF := fifthDefect_eq_clearedDelta810 h a7 a6 a5 a4 a3 b9 b8 b7
      b6 b5 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedFifthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, h, a7, a6, a5, a4, a3, b8,
      b7, b6, b5, deltaResidual810, alphaResidual810, betaResidual810, hf6,
      hf5, hf4, hf3, hg5, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (131072 * eps0) * h0 ^ 35) := by
    rw [hclear, heps0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨131072 * eps0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

set_option maxHeartbeats 8000000 in
/-- Finite local initial packet: the degree-one scale divides the
subleading octic coefficient to order six, the next octic coefficient
to order three, the first unused decic coefficient to order five, `q₇`
to order two, and `q₉` to order eight. -/
theorem nonzeroFace810_linearRoot_fifthInitialPacket
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
    h0 ^ 6 ∣ p.coeff 7 ∧ h0 ^ 3 ∣ p.coeff 6 ∧ h0 ^ 5 ∣ q.coeff 8 ∧
      h0 ^ 2 ∣ q.coeff 7 ∧ h0 ^ 8 ∣ q.coeff 9 := by
  obtain ⟨alpha, hM⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨gamma, hT⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨delta, hU⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨hp7pow5, hp6pow2, hq8pow4, hq7pow, _hq9pow7⟩ :=
    nonzeroFace810_linearRoot_fourthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  obtain ⟨t1, ht1⟩ := hp7pow5
  obtain ⟨v2, hv2⟩ := hp6pow2
  obtain ⟨s2, hs2⟩ := hq8pow4
  obtain ⟨w1, hw1⟩ := hq7pow
  have hM0 :
      (32 : k[X]) * s2 - (40 : k[X]) * v2 - (5 : k[X]) * t1 ^ 2 +
        (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 2 =
        Polynomial.C alpha * h0 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 10 hh0)
    calc
      h0 ^ 10 *
            ((32 : k[X]) * s2 - (40 : k[X]) * v2 -
                (5 : k[X]) * t1 ^ 2 +
              (9 : k[X]) * Polynomial.C lambda * t1 * h0 ^ 2) =
          localClearedSecondDefect810 h0 (p.coeff 7) (p.coeff 6)
            (q.coeff 8) lambda := by
        simp only [localClearedSecondDefect810, ht1, hv2, hs2]
        ring
      _ = Polynomial.C alpha * h0 ^ 14 := hM
      _ = h0 ^ 10 * (Polynomial.C alpha * h0 ^ 4) := by ring
  have hT0 :
      (100 : k[X]) * t1 ^ 3 - (512 : k[X]) * t1 * s2 +
          (480 : k[X]) * t1 * v2 + (512 : k[X]) * w1 -
        (640 : k[X]) * p.coeff 5 * h0 +
          (144 : k[X]) * Polynomial.C lambda * v2 * h0 ^ 2 -
        (135 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 2 =
        Polynomial.C gamma * h0 ^ 6 := by
    apply mul_left_cancel₀ (pow_ne_zero 15 hh0)
    calc
      h0 ^ 15 *
            ((100 : k[X]) * t1 ^ 3 - (512 : k[X]) * t1 * s2 +
                (480 : k[X]) * t1 * v2 + (512 : k[X]) * w1 -
              (640 : k[X]) * p.coeff 5 * h0 +
                (144 : k[X]) * Polynomial.C lambda * v2 * h0 ^ 2 -
              (135 : k[X]) * Polynomial.C lambda * t1 ^ 2 * h0 ^ 2) =
          localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [localClearedThirdDefect810, ht1, hv2, hs2, hw1]
        ring
      _ = Polynomial.C gamma * h0 ^ 21 := hT
      _ = h0 ^ 15 * (Polynomial.C gamma * h0 ^ 6) := by ring
  have hU0 :
      (1792 : k[X]) * s2 * t1 ^ 2 - (2048 : k[X]) * s2 * v2 -
          (385 : k[X]) * t1 ^ 4 - (1120 : k[X]) * t1 ^ 2 * v2 -
        (1792 : k[X]) * t1 * w1 + (2240 : k[X]) * v2 ^ 2 +
          (1600 : k[X]) * p.coeff 5 * t1 * h0 +
        (2048 : k[X]) * q.coeff 6 * h0 ^ 2 +
          (462 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 2 -
        (1008 : k[X]) * Polynomial.C lambda * t1 * v2 * h0 ^ 2 +
          (576 : k[X]) * Polynomial.C lambda * p.coeff 5 * h0 ^ 3 -
        (2560 : k[X]) * p.coeff 4 * h0 ^ 4 =
        Polynomial.C delta * h0 ^ 8 := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hh0)
    calc
      h0 ^ 20 *
            ((1792 : k[X]) * s2 * t1 ^ 2 - (2048 : k[X]) * s2 * v2 -
                (385 : k[X]) * t1 ^ 4 - (1120 : k[X]) * t1 ^ 2 * v2 -
              (1792 : k[X]) * t1 * w1 + (2240 : k[X]) * v2 ^ 2 +
                (1600 : k[X]) * p.coeff 5 * t1 * h0 +
              (2048 : k[X]) * q.coeff 6 * h0 ^ 2 +
                (462 : k[X]) * Polynomial.C lambda * t1 ^ 3 * h0 ^ 2 -
              (1008 : k[X]) * Polynomial.C lambda * t1 * v2 * h0 ^ 2 +
                (576 : k[X]) * Polynomial.C lambda * p.coeff 5 *
                    h0 ^ 3 -
              (2560 : k[X]) * p.coeff 4 * h0 ^ 4) =
          localClearedFourthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7)
            (q.coeff 6) lambda := by
        simp only [localClearedFourthDefect810, ht1, hv2, hs2, hw1]
        ring
      _ = Polynomial.C delta * h0 ^ 28 := hU
      _ = h0 ^ 20 * (Polynomial.C delta * h0 ^ 8) := by ring
  have hV0 :
      -(93184 : k[X]) * s2 * t1 ^ 3 + (212992 : k[X]) * s2 * t1 * v2 +
          (21112 : k[X]) * t1 ^ 5 + (29120 : k[X]) * t1 ^ 3 * v2 +
        (93184 : k[X]) * t1 ^ 2 * w1 - (199680 : k[X]) * t1 * v2 ^ 2 -
          (114688 : k[X]) * v2 * w1 +
        (-(131072 : k[X]) * p.coeff 5 * s2 -
              (49920 : k[X]) * p.coeff 5 * t1 ^ 2 +
            (266240 : k[X]) * p.coeff 5 * v2) * h0 +
          (-(98304 : k[X]) * q.coeff 6 * t1 -
                (23751 : k[X]) * Polynomial.C lambda * t1 ^ 4 +
              (78624 : k[X]) * Polynomial.C lambda * t1 ^ 2 * v2 -
            (29952 : k[X]) * Polynomial.C lambda * v2 ^ 2) * h0 ^ 2 -
        (59904 : k[X]) * Polynomial.C lambda * p.coeff 5 * t1 * h0 ^ 3 +
          (81920 : k[X]) * p.coeff 4 * t1 * h0 ^ 4 +
        (131072 : k[X]) * q.coeff 5 * h0 ^ 5 +
          (36864 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 6 -
        (163840 : k[X]) * p.coeff 3 * h0 ^ 7 =
        Polynomial.C eps * h0 ^ 10 := by
    apply mul_left_cancel₀ (pow_ne_zero 25 hh0)
    calc
      h0 ^ 25 *
            (-(93184 : k[X]) * s2 * t1 ^ 3 +
                (212992 : k[X]) * s2 * t1 * v2 +
              (21112 : k[X]) * t1 ^ 5 + (29120 : k[X]) * t1 ^ 3 * v2 +
                (93184 : k[X]) * t1 ^ 2 * w1 -
              (199680 : k[X]) * t1 * v2 ^ 2 -
                (114688 : k[X]) * v2 * w1 +
              (-(131072 : k[X]) * p.coeff 5 * s2 -
                    (49920 : k[X]) * p.coeff 5 * t1 ^ 2 +
                  (266240 : k[X]) * p.coeff 5 * v2) * h0 +
                (-(98304 : k[X]) * q.coeff 6 * t1 -
                      (23751 : k[X]) * Polynomial.C lambda * t1 ^ 4 +
                    (78624 : k[X]) * Polynomial.C lambda * t1 ^ 2 *
                        v2 -
                  (29952 : k[X]) * Polynomial.C lambda * v2 ^ 2) *
                    h0 ^ 2 -
              (59904 : k[X]) * Polynomial.C lambda * p.coeff 5 * t1 *
                  h0 ^ 3 +
                (81920 : k[X]) * p.coeff 4 * t1 * h0 ^ 4 +
              (131072 : k[X]) * q.coeff 5 * h0 ^ 5 +
                (36864 : k[X]) * Polynomial.C lambda * p.coeff 4 *
                    h0 ^ 6 -
              (163840 : k[X]) * p.coeff 3 * h0 ^ 7) =
          localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda := by
        simp only [localClearedFifthDefect810, ht1, hv2, hs2, hw1]
        ring
      _ = Polynomial.C eps * h0 ^ 35 := hVrel
      _ = h0 ^ 25 * (Polynomial.C eps * h0 ^ 10) := by ring
  have hMroot : (32 : k) * s2.eval a - (40 : k) * v2.eval a -
      (5 : k) * (t1.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hM0
    simpa [hroot] using heval
  have hTroot : (100 : k) * (t1.eval a) ^ 3 -
      (512 : k) * t1.eval a * s2.eval a +
        (480 : k) * t1.eval a * v2.eval a +
          (512 : k) * w1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hT0
    simpa [hroot] using heval
  have hUroot : (1792 : k) * s2.eval a * (t1.eval a) ^ 2 -
      (2048 : k) * s2.eval a * v2.eval a -
        (385 : k) * (t1.eval a) ^ 4 -
          (1120 : k) * (t1.eval a) ^ 2 * v2.eval a -
        (1792 : k) * t1.eval a * w1.eval a +
          (2240 : k) * (v2.eval a) ^ 2 = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hU0
    simpa [hroot] using heval
  have hVroot : -(93184 : k) * s2.eval a * (t1.eval a) ^ 3 +
      (212992 : k) * s2.eval a * t1.eval a * v2.eval a +
        (21112 : k) * (t1.eval a) ^ 5 +
          (29120 : k) * (t1.eval a) ^ 3 * v2.eval a +
        (93184 : k) * (t1.eval a) ^ 2 * w1.eval a -
          (199680 : k) * t1.eval a * (v2.eval a) ^ 2 -
        (114688 : k) * v2.eval a * w1.eval a = 0 := by
    have heval := congrArg (fun r : k[X] => r.eval a) hV0
    simpa [hroot] using heval
  obtain ⟨ht10, hv20, hs20, hw10⟩ :=
    fifthFace_rootScalars_vanish810 (t1.eval a) (v2.eval a) (s2.eval a)
      (w1.eval a) hMroot hTroot hUroot hVroot
  have ht1_div : h0 ∣ t1 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 t1 a hh0degree hroot ht10
  have hv2_div : h0 ∣ v2 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 v2 a hh0degree hroot hv20
  have hs2_div : h0 ∣ s2 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 s2 a hh0degree hroot hs20
  have hw1_div : h0 ∣ w1 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 w1 a hh0degree hroot hw10
  have hp7pow : h0 ^ 6 ∣ p.coeff 7 := by
    obtain ⟨t2, ht2⟩ := ht1_div
    refine ⟨t2, ?_⟩
    rw [ht1, ht2]
    ring
  have hp6pow : h0 ^ 3 ∣ p.coeff 6 := by
    obtain ⟨v3, hv3⟩ := hv2_div
    refine ⟨v3, ?_⟩
    rw [hv2, hv3]
    ring
  have hq8pow : h0 ^ 5 ∣ q.coeff 8 := by
    obtain ⟨s3, hs3⟩ := hs2_div
    refine ⟨s3, ?_⟩
    rw [hs2, hs3]
    ring
  have hq7pow2 : h0 ^ 2 ∣ q.coeff 7 := by
    obtain ⟨w2, hw2⟩ := hw1_div
    refine ⟨w2, ?_⟩
    rw [hw1, hw2]
    ring
  have hq9pow : h0 ^ 8 ∣ q.coeff 9 := by
    have h4 : (4 : k) ≠ 0 := by norm_num
    obtain ⟨t2, ht2⟩ := ht1_div
    have hp7t2 : p.coeff 7 = h0 ^ 6 * t2 := by
      rw [ht1, ht2]
      ring
    have hN' :
        (4 : k[X]) * q.coeff 9 =
          (5 : k[X]) * p.coeff 7 * h0 ^ 2 -
            Polynomial.C lambda * h0 ^ 9 := by
      have : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := hN
      rw [hH] at this
      linear_combination -this
    have hform :
        (4 : k[X]) * q.coeff 9 =
          h0 ^ 8 * ((5 : k[X]) * t2 - Polynomial.C lambda * h0) := by
      rw [hN', hp7t2]
      ring
    have hC4 : Polynomial.C (4 : k) = (4 : k[X]) :=
      Polynomial.C_eq_natCast 4
    have hq9eq : q.coeff 9 =
        C ((4 : k)⁻¹) * ((4 : k[X]) * q.coeff 9) := by
      have hone : (C ((4 : k)⁻¹) * C (4 : k) : k[X]) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h4, map_one]
      calc
        q.coeff 9 = (1 : k[X]) * q.coeff 9 := (one_mul _).symm
        _ = (C ((4 : k)⁻¹) * C (4 : k)) * q.coeff 9 := by rw [hone]
        _ = C ((4 : k)⁻¹) * (C (4 : k) * q.coeff 9) := mul_assoc _ _ _
        _ = C ((4 : k)⁻¹) * ((4 : k[X]) * q.coeff 9) := by rw [hC4]
    refine ⟨C ((4 : k)⁻¹) *
        ((5 : k[X]) * t2 - Polynomial.C lambda * h0), ?_⟩
    rw [hq9eq, hform]
    ring
  exact ⟨hp7pow, hp6pow, hq8pow, hq7pow2, hq9pow⟩

/-- Source-facing fifth integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_fifthDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eps : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
            (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda =
          Polynomial.C eps * h0 ^ 35 := by
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
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, eps, hh0, hlambda, hh0degree, hH, hN', hVrel⟩

/-- Finite local initial packet of a normalized scale-two `(8,10)`
nonzero face: the degree-one scale divides `p₇` to order six, `p₆` to
order three, `q₈` to order five, `q₇` to order two, and `q₉` to order
eight. -/
theorem normalized810ScaleTwo_nonzeroFace_fifthInitialPacket
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
        h0 ^ 6 ∣ p.coeff 7 ∧ h0 ^ 3 ∣ p.coeff 6 ∧ h0 ^ 5 ∣ q.coeff 8 ∧
        h0 ^ 2 ∣ q.coeff 7 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
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
  obtain ⟨hp7, hp6, hq8, hq7, hq9⟩ :=
    nonzeroFace810_linearRoot_fifthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hp7, hp6, hq8,
    hq7, hq9, hN'⟩

end NonzeroFifthFace810

#print axioms fifthCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_12_monicOcticDecic
#print axioms fifthDefect_eq_clearedDelta810
#print axioms nonzeroFace810_fifthDefectPowerRelation
#print axioms nonzeroFace810_linearRoot_fifthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_fifthDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_fifthInitialPacket

end Max11DegreeRoutes
