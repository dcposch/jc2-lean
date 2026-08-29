import LowScale810ScaleTwoSixthFace

/-! # Scale-two seventh face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the sixth face supplies the degree-`11` integral
and the jet `h⁶ ∣ p₇`, `h³ ∣ p₆`, `h ∣ p₅`, `h⁵ ∣ q₈`, `h³ ∣ q₇`,
`h⁸ ∣ q₉`.  The next Keller coefficient is the degree-`10` Jacobian
row.  After the same octic depression that kills `z⁷`, that row is
`10 F' + 9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - 3 D P' - 4 C Q'
- 5 B R' - 6 A S' - 8 U' = 0`.  The resulting first integral clears to
a polynomial defect `X` of weight forty-nine.

Evaluating the second, third, fourth, fifth, and seventh defects
together at the root of `h` upgrades the jet to `h⁴ ∣ p₆`, `h⁶ ∣ q₈`,
and `h ∣ q₆`, and forces the mixed identity
`4 (q₇/h³)(a) = 5 (p₅/h)(a)`.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The seventh row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  It is the source of the first mixed octic/decic
`z¹`/`z³` defect after the degree-`11` integral. -/
theorem seventhCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 7).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 3).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 4).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 5).derivative +
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

/-! ## Octic `z¹` and decic `z³` coordinates -/

section Depression810Seventh

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z¹` coefficient. -/
def depressedF810 (h r a7 a6 a5 a4 a3 a2 a1 : F) : F :=
  depressedU68 h r a7 a6 a5 a4 a3 a2 a1

/-- Depressed decic `z³` coefficient. -/
def depressedU810 (h r b9 b8 b7 b6 b5 b4 b3 : F) : F :=
  -120 * r ^ 7 + 84 * (b9 / h ^ 9) * r ^ 6 -
    56 * (b8 / h ^ 8) * r ^ 5 + 35 * (b7 / h ^ 7) * r ^ 4 -
    20 * (b6 / h ^ 6) * r ^ 3 + 10 * (b5 / h ^ 5) * r ^ 2 -
    4 * (b4 / h ^ 4) * r + b3 / h ^ 3

/-- First residual of the degree-`10` row. -/
def zetaResidual810 (L A B C0 D0 E0 F0 P Q R S0 U0 : F) : F :=
  U0 - ((5 / 4 : F) * F0 + (9 / 8 : F) * L * E0 +
    alphaResidual810 A P * D0 +
    (7 / 8 : F) * betaResidual810 L A B Q * C0 +
    (3 / 4 : F) * gammaResidual810 L A B C0 P R * B +
    (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A +
    (5 / 16 : F) * A * D0 + (5 / 16 : F) * B * C0 -
    (7 / 128 : F) * betaResidual810 L A B Q * A ^ 2 -
    (15 / 128 : F) * A ^ 2 * B - (21 / 1024 : F) * L * A ^ 3 +
    (9 / 64 : F) * L * A * C0 + (9 / 128 : F) * L * B ^ 2)

/-- Polynomial numerator of `16777216 h⁴⁹ ζ` on the ninth-power face. -/
def localClearedSeventhDefect810
    (h a7 a6 a5 a4 a3 a2 a1 b8 b7 b6 b5 b4 b3 : F[X]) (lambda : F) :
    F[X] :=
  -(20971520 : F[X]) * a1 * h ^ 48 +
    (4718592 : F[X]) * a2 * Polynomial.C lambda * h ^ 47 +
    (5242880 : F[X]) * a2 * a7 * h ^ 40 +
    (28835840 : F[X]) * a3 * a6 * h ^ 40 -
    (6488064 : F[X]) * a3 * a7 * Polynomial.C lambda * h ^ 39 -
    (16777216 : F[X]) * a3 * b8 * h ^ 38 -
    (1802240 : F[X]) * a3 * a7 ^ 2 * h ^ 32 +
    (28835840 : F[X]) * a4 * a5 * h ^ 40 -
    (6488064 : F[X]) * a4 * a6 * Polynomial.C lambda * h ^ 39 -
    (14680064 : F[X]) * a4 * b7 * h ^ 38 -
    (36044800 : F[X]) * a4 * a6 * a7 * h ^ 32 +
    (7704576 : F[X]) * a4 * a7 ^ 2 * Polynomial.C lambda * h ^ 31 +
    (23068672 : F[X]) * a4 * a7 * b8 * h ^ 30 -
    (3244032 : F[X]) * a5 ^ 2 * Polynomial.C lambda * h ^ 39 -
    (12582912 : F[X]) * a5 * b6 * h ^ 38 -
    (18022400 : F[X]) * a5 ^ 2 * a7 * h ^ 32 -
    (34242560 : F[X]) * a5 * a6 ^ 2 * h ^ 32 +
    (15409152 : F[X]) * a5 * a6 * a7 * Polynomial.C lambda * h ^ 31 +
    (20185088 : F[X]) * a5 * a7 * b7 * h ^ 30 +
    (23068672 : F[X]) * a5 * a6 * b8 * h ^ 30 +
    (38522880 : F[X]) * a5 * a6 * a7 ^ 2 * h ^ 24 -
    (8667648 : F[X]) * a5 * a7 ^ 3 * Polynomial.C lambda * h ^ 23 -
    (27394048 : F[X]) * a5 * a7 ^ 2 * b8 * h ^ 22 +
    (1203840 : F[X]) * a5 * a7 ^ 4 * h ^ 16 -
    (10485760 : F[X]) * a6 * b5 * h ^ 38 +
    (2568192 : F[X]) * a6 ^ 3 * Polynomial.C lambda * h ^ 31 +
    (10092544 : F[X]) * a6 ^ 2 * b7 * h ^ 30 +
    (17301504 : F[X]) * a6 * a7 * b6 * h ^ 30 +
    (25681920 : F[X]) * a6 ^ 3 * a7 * h ^ 24 -
    (13001472 : F[X]) * a6 ^ 2 * a7 ^ 2 * Polynomial.C lambda * h ^ 23 -
    (23969792 : F[X]) * a6 * a7 ^ 2 * b7 * h ^ 22 -
    (27394048 : F[X]) * a6 ^ 2 * a7 * b8 * h ^ 22 -
    (19261440 : F[X]) * a6 ^ 2 * a7 ^ 3 * h ^ 16 +
    (9480240 : F[X]) * a6 * a7 ^ 4 * Polynomial.C lambda * h ^ 15 +
    (30818304 : F[X]) * a6 * a7 ^ 3 * b8 * h ^ 14 -
    (2106720 : F[X]) * a6 * a7 ^ 5 * h ^ 8 -
    (8388608 : F[X]) * a7 * b4 * h ^ 38 +
    (7208960 : F[X]) * a7 ^ 2 * b5 * h ^ 30 -
    (6848512 : F[X]) * a7 ^ 3 * b6 * h ^ 22 +
    (6741504 : F[X]) * a7 ^ 4 * b7 * h ^ 14 -
    (1698543 : F[X]) * a7 ^ 6 * Polynomial.C lambda * h ^ 7 -
    (6741504 : F[X]) * a7 ^ 5 * b8 * h ^ 6 +
    (1617660 : F[X]) * a7 ^ 7 +
    (16777216 : F[X]) * b3 * h ^ 46

set_option linter.unusedSectionVars false in
theorem coeff_depressedOctic68_one
    (L P Q R S T0 U V : F) :
    (depressedOctic68 L P Q R S T0 U V).coeff 1 = U := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z¹` coordinate. -/
theorem depressedF810_eq_cleared
    (h a7 a6 a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
      (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
          6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
          160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
          3 * a7 ^ 7) /
        (131072 * h ^ 49) := by
  simp only [depressedF810, depressedU68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z³` coordinate on the
ninth-power face. -/
theorem depressedU810_eq_cleared
    (h a7 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
      (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
          448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
          10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
          131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
        (262144 * h ^ 49) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4pow : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedU810, octicDepressionR810]
  have hrewrite :
      -120 * (a7 / (8 * h ^ 7)) ^ 7 +
          84 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 6 -
        56 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 5 +
          35 * (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) ^ 4 -
        20 * (b6 / h ^ 6) * (a7 / (8 * h ^ 7)) ^ 3 +
          10 * (b5 / h ^ 5) * (a7 / (8 * h ^ 7)) ^ 2 -
        4 * (b4 / h ^ 4) * (a7 / (8 * h ^ 7)) + b3 / h ^ 3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) := by
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh49, h262144]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh49, h262144]
    ring
  exact hrewrite

set_option maxHeartbeats 16000000 in
/-- Clearing the first integral
`U - (5/4) F - (9/8) L E - α D - (7/8) β C - (3/4) γ B - (5/8) δ A
- (5/16) A D - (5/16) B C + (7/128) β A² + (15/128) A² B
+ (21/1024) L A³ - (9/64) L A C - (9/128) L B²`
against `h⁴⁹` on the ninth-power face. -/
theorem seventhDefect_eq_clearedZeta810
    (h a7 a6 a5 a4 a3 a2 a1 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (16777216 : F) * h ^ 49 *
        zetaResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3) =
  -(20971520 : F) * a1 * h ^ 48 +
    (4718592 : F) * a2 * lambda * h ^ 47 +
    (5242880 : F) * a2 * a7 * h ^ 40 +
    (28835840 : F) * a3 * a6 * h ^ 40 -
    (6488064 : F) * a3 * a7 * lambda * h ^ 39 -
    (16777216 : F) * a3 * b8 * h ^ 38 -
    (1802240 : F) * a3 * a7 ^ 2 * h ^ 32 +
    (28835840 : F) * a4 * a5 * h ^ 40 -
    (6488064 : F) * a4 * a6 * lambda * h ^ 39 -
    (14680064 : F) * a4 * b7 * h ^ 38 -
    (36044800 : F) * a4 * a6 * a7 * h ^ 32 +
    (7704576 : F) * a4 * a7 ^ 2 * lambda * h ^ 31 +
    (23068672 : F) * a4 * a7 * b8 * h ^ 30 -
    (3244032 : F) * a5 ^ 2 * lambda * h ^ 39 -
    (12582912 : F) * a5 * b6 * h ^ 38 -
    (18022400 : F) * a5 ^ 2 * a7 * h ^ 32 -
    (34242560 : F) * a5 * a6 ^ 2 * h ^ 32 +
    (15409152 : F) * a5 * a6 * a7 * lambda * h ^ 31 +
    (20185088 : F) * a5 * a7 * b7 * h ^ 30 +
    (23068672 : F) * a5 * a6 * b8 * h ^ 30 +
    (38522880 : F) * a5 * a6 * a7 ^ 2 * h ^ 24 -
    (8667648 : F) * a5 * a7 ^ 3 * lambda * h ^ 23 -
    (27394048 : F) * a5 * a7 ^ 2 * b8 * h ^ 22 +
    (1203840 : F) * a5 * a7 ^ 4 * h ^ 16 -
    (10485760 : F) * a6 * b5 * h ^ 38 +
    (2568192 : F) * a6 ^ 3 * lambda * h ^ 31 +
    (10092544 : F) * a6 ^ 2 * b7 * h ^ 30 +
    (17301504 : F) * a6 * a7 * b6 * h ^ 30 +
    (25681920 : F) * a6 ^ 3 * a7 * h ^ 24 -
    (13001472 : F) * a6 ^ 2 * a7 ^ 2 * lambda * h ^ 23 -
    (23969792 : F) * a6 * a7 ^ 2 * b7 * h ^ 22 -
    (27394048 : F) * a6 ^ 2 * a7 * b8 * h ^ 22 -
    (19261440 : F) * a6 ^ 2 * a7 ^ 3 * h ^ 16 +
    (9480240 : F) * a6 * a7 ^ 4 * lambda * h ^ 15 +
    (30818304 : F) * a6 * a7 ^ 3 * b8 * h ^ 14 -
    (2106720 : F) * a6 * a7 ^ 5 * h ^ 8 -
    (8388608 : F) * a7 * b4 * h ^ 38 +
    (7208960 : F) * a7 ^ 2 * b5 * h ^ 30 -
    (6848512 : F) * a7 ^ 3 * b6 * h ^ 22 +
    (6741504 : F) * a7 ^ 4 * b7 * h ^ 14 -
    (1698543 : F) * a7 ^ 6 * lambda * h ^ 7 -
    (6741504 : F) * a7 ^ 5 * b8 * h ^ 6 +
    (1617660 : F) * a7 ^ 7 +
    (16777216 : F) * b3 * h ^ 46 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
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
  have hF0 :
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 =
        (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
            6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
            160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
            3 * a7 ^ 7) /
          (131072 * h ^ 49) :=
    depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh
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
  have hS :
      depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
        (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
            896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
            6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) /
          (8192 * h ^ 35) :=
    depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN
  have hU :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  simp only [zetaResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hP, hQ, hR,
    hS, hU, alphaResidual810, betaResidual810, gammaResidual810,
    deltaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h1024, h2048, h8192,
    h65536, h131072, h262144, hh14, hh21, hh28, hh35, hh42, hh49]
  ring

end Depression810Seventh

/-! ## Degree-`10` depressed Jacobian coefficient -/

section DepressedRow810Seventh

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`10` Jacobian coefficient is
exactly `10 F' + 9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - 3 D P'
- 4 C Q' - 5 B R' - 6 A S' - 8 U'`. -/
theorem differentialJacobian_coeff_10_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 10 =
      (10 : F) * d (f.coeff 1) + (9 : F) * g.coeff 9 * d (f.coeff 2) +
        (8 : F) * g.coeff 8 * d (f.coeff 3) +
        (7 : F) * g.coeff 7 * d (f.coeff 4) +
        (6 : F) * g.coeff 6 * d (f.coeff 5) +
        (5 : F) * g.coeff 5 * d (f.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 8) -
          (4 : F) * f.coeff 4 * d (g.coeff 7) -
          (5 : F) * f.coeff 5 * d (g.coeff 6) -
          (6 : F) * f.coeff 6 * d (g.coeff 5) -
          (8 : F) * d (g.coeff 3) := by
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
  have hmem64 : ((6, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem73 : ((7, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 10 =
        (10 : F) * d (f.coeff 1) +
          (9 : F) * g.coeff 9 * d (f.coeff 2) +
          (8 : F) * g.coeff 8 * d (f.coeff 3) +
          (7 : F) * g.coeff 7 * d (f.coeff 4) +
          (6 : F) * g.coeff 6 * d (f.coeff 5) +
          (5 : F) * g.coeff 5 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne19_28 : ((1, 9) : ℕ × ℕ) ≠ (2, 8) := by decide
    have hne19_37 : ((1, 9) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne19_46 : ((1, 9) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne19_55 : ((1, 9) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne19_64 : ((1, 9) : ℕ × ℕ) ≠ (6, 4) := by decide
    have hne28_37 : ((2, 8) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne28_46 : ((2, 8) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne28_55 : ((2, 8) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne28_64 : ((2, 8) : ℕ × ℕ) ≠ (6, 4) := by decide
    have hne37_46 : ((3, 7) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne37_55 : ((3, 7) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne37_64 : ((3, 7) : ℕ × ℕ) ≠ (6, 4) := by decide
    have hne46_55 : ((4, 6) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne46_64 : ((4, 6) : ℕ × ℕ) ≠ (6, 4) := by decide
    have hne55_64 : ((5, 5) : ℕ × ℕ) ≠ (6, 4) := by decide
    have hsubset :
        ({(1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (10 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb
      · subst b; exact hmem19
      · subst b; exact hmem28
      · subst b; exact hmem37
      · subst b; exact hmem46
      · subst b; exact hmem55
      · subst b; exact hmem64
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4)} :
              Finset (ℕ × ℕ)),
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
      have hne55 : b ≠ (5, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne64 : b ≠ (6, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne1 : b.1 ≠ 1 := by
          intro h1; apply hne19; ext; exact h1; omega
        have hne2 : b.1 ≠ 2 := by
          intro h2; apply hne28; ext; exact h2; omega
        have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne37; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne46; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne55; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne64; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4)} :
            Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 1 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 4 := by
      rw [Finset.sum_insert (by simp [hne19_28, hne19_37, hne19_46, hne19_55,
            hne19_64]),
        Finset.sum_insert (by simp [hne28_37, hne28_46, hne28_55, hne28_64]),
        Finset.sum_insert (by simp [hne37_46, hne37_55, hne37_64]),
        Finset.sum_insert (by simp [hne46_55, hne46_64]),
        Finset.sum_insert (by simp [hne55_64]), Finset.sum_singleton]
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
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder9, hder8, hder7, hder6, hder5, hder4]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 10 =
        (3 : F) * f.coeff 3 * d (g.coeff 8) +
          (4 : F) * f.coeff 4 * d (g.coeff 7) +
          (5 : F) * f.coeff 5 * d (g.coeff 6) +
          (6 : F) * f.coeff 6 * d (g.coeff 5) +
          (8 : F) * d (g.coeff 3) := by
    rw [Polynomial.coeff_mul]
    have hne28_37 : ((2, 8) : ℕ × ℕ) ≠ (3, 7) := by decide
    have hne28_46 : ((2, 8) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne28_55 : ((2, 8) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne28_73 : ((2, 8) : ℕ × ℕ) ≠ (7, 3) := by decide
    have hne37_46 : ((3, 7) : ℕ × ℕ) ≠ (4, 6) := by decide
    have hne37_55 : ((3, 7) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne37_73 : ((3, 7) : ℕ × ℕ) ≠ (7, 3) := by decide
    have hne46_55 : ((4, 6) : ℕ × ℕ) ≠ (5, 5) := by decide
    have hne46_73 : ((4, 6) : ℕ × ℕ) ≠ (7, 3) := by decide
    have hne55_73 : ((5, 5) : ℕ × ℕ) ≠ (7, 3) := by decide
    have hsubset :
        ({(2, 8), (3, 7), (4, 6), (5, 5), (7, 3)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (10 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem28
      · subst b; exact hmem37
      · subst b; exact hmem46
      · subst b; exact hmem55
      · subst b; exact hmem73
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (10 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(2, 8), (3, 7), (4, 6), (5, 5), (7, 3)} : Finset (ℕ × ℕ)),
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
      have hne46 : b ≠ (4, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne55 : b ≠ (5, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne73 : b ≠ (7, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne2 : b.1 ≠ 2 := by
            intro h2; apply hne28; ext; exact h2; omega
          have hne3 : b.1 ≠ 3 := by
            intro h3; apply hne37; ext; exact h3; omega
          have hne4 : b.1 ≠ 4 := by
            intro h4; apply hne46; ext; exact h4; omega
          have hne5 : b.1 ≠ 5 := by
            intro h5; apply hne55; ext; exact h5; omega
          have hne7 : b.1 ≠ 7 := by
            intro h7; apply hne73; ext; exact h7; omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(2, 8), (3, 7), (4, 6), (5, 5), (7, 3)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 2 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 3 := by
      rw [Finset.sum_insert (by simp [hne28_37, hne28_46, hne28_55, hne28_73]),
        Finset.sum_insert (by simp [hne37_46, hne37_55, hne37_73]),
        Finset.sum_insert (by simp [hne46_55, hne46_73]),
        Finset.sum_insert (by simp [hne55_73]), Finset.sum_singleton]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
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
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      hder2, hder3, hder4, hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

theorem zetaResidual810_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 F0 P Q R S0 U0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hrow : (10 : F) * d F0 + (9 : F) * L * d E0 +
        (8 : F) * P * d D0 + (7 : F) * Q * d C0 +
        (6 : F) * R * d B + (5 : F) * S0 * d A -
        (3 : F) * D0 * d P - (4 : F) * C0 * d Q -
        (5 : F) * B * d R - (6 : F) * A * d S0 -
        (8 : F) * d U0 = 0) :
    d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0 := by
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h15128 : d (15 / 128 : F) = 0 := by
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    simp [Derivation.leibniz_div, h128, h15]
  have h211024 : d (21 / 1024 : F) = 0 := by
    have h21 : d (21 : F) = 0 := d.map_natCast 21
    simp [Derivation.leibniz_div, h1024, h21]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
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
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          (P - (5 / 4 : F) * A) * d B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    simp only [deltaResidual810, alphaResidual810, betaResidual810, map_sub,
      map_add, Derivation.leibniz, h54, h98, h78, h516, h9128, hL, zero_mul,
      add_zero, mul_zero, pow_two, hsq, hPderiv, hQderiv]
    ring
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hUderiv :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        P * d D0 + (7 / 8 : F) * Q * d C0 + (3 / 4 : F) * R * d B +
        (5 / 8 : F) * S0 * d A - (3 / 8 : F) * D0 * d P -
        (1 / 2 : F) * C0 * d Q - (5 / 8 : F) * B * d R -
        (3 / 4 : F) * A * d S0 := by
    linear_combination (-1 / 8 : F) * hrow
  simp only [zetaResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, map_sub, map_add, Derivation.leibniz,
    h54, h98, h78, h34, h58, h516, h532, h7128, h15128, h211024, h964,
    h9128, hL, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
  rw [hUderiv, hPderiv, hQderiv, hRderiv, hSderiv]
  ring

end DepressedRow810Seventh

/-! ## Affine depression of a degree-ten source, `z³` coefficient -/

section AffineDecic810Seventh

variable {k : Type*} [Field k] [CharZero k]

/-- The `z³` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff3_810
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

end AffineDecic810Seventh

/-! ## Local scalar identities at a simple root -/

section SeventhFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

def secondJetParen810
    (h t0 v0 s0 : F[X]) (lambda : F) : F[X] :=
  (32 : F[X]) * s0 - (40 : F[X]) * v0 -
    (5 : F[X]) * t0 ^ 2 * h +
    (9 : F[X]) * Polynomial.C lambda * t0 * h ^ 2

def thirdJetParen810_sixth
    (h t0 v0 s0 w0 u0 : F[X]) (lambda : F) : F[X] :=
  -(512 : F[X]) * s0 * t0 + (480 : F[X]) * t0 * v0 -
    (640 : F[X]) * u0 + (512 : F[X]) * w0 +
    ((100 : F[X]) * t0 ^ 3 +
        (144 : F[X]) * Polynomial.C lambda * v0) * h -
    (135 : F[X]) * Polynomial.C lambda * t0 ^ 2 * h ^ 2

def fourthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 b6 : F[X]) (lambda : F) : F[X] :=
  (2048 : F[X]) * b6 - (2048 : F[X]) * s0 * v0 +
    (2240 : F[X]) * v0 ^ 2 +
    ((1792 : F[X]) * s0 * t0 ^ 2 - (1120 : F[X]) * t0 ^ 2 * v0 +
        (1600 : F[X]) * t0 * u0 - (1792 : F[X]) * t0 * w0) * h +
    (-(2560 : F[X]) * a4 - (1008 : F[X]) * Polynomial.C lambda * t0 * v0 +
        (576 : F[X]) * Polynomial.C lambda * u0 -
        (385 : F[X]) * t0 ^ 4) * h ^ 2 +
    (462 : F[X]) * Polynomial.C lambda * t0 ^ 3 * h ^ 3

def fifthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 a3 b6 b5 : F[X]) (lambda : F) : F[X] :=
  -(98304 : F[X]) * b6 * t0 + (212992 : F[X]) * s0 * t0 * v0 -
    (131072 : F[X]) * s0 * u0 - (199680 : F[X]) * t0 * v0 ^ 2 +
    (266240 : F[X]) * u0 * v0 - (114688 : F[X]) * v0 * w0 +
    (-(29952 : F[X]) * Polynomial.C lambda * v0 ^ 2 -
        (93184 : F[X]) * s0 * t0 ^ 3 + (29120 : F[X]) * t0 ^ 3 * v0 -
        (49920 : F[X]) * t0 ^ 2 * u0 + (93184 : F[X]) * t0 ^ 2 * w0) * h +
    ((81920 : F[X]) * a4 * t0 + (131072 : F[X]) * b5 +
        (78624 : F[X]) * Polynomial.C lambda * t0 ^ 2 * v0 -
        (59904 : F[X]) * Polynomial.C lambda * t0 * u0 +
        (21112 : F[X]) * t0 ^ 5) * h ^ 2 +
    ((36864 : F[X]) * a4 * Polynomial.C lambda -
        (23751 : F[X]) * Polynomial.C lambda * t0 ^ 4) * h ^ 3 -
    (163840 : F[X]) * a3 * h ^ 4

def seventhJetParen810
    (h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 : F[X]) (lambda : F) :
    F[X] :=
  -(34242560 : F[X]) * v0 ^ 2 * u0 -
    (20971520 : F[X]) * a1 * h ^ 9 -
    (12582912 : F[X]) * u0 * b6 +
    (1617660 : F[X]) * t0 ^ 7 * h ^ 3 +
    (10092544 : F[X]) * v0 ^ 2 * w0 +
    (16777216 : F[X]) * b3 * h ^ 7 +
    (25681920 : F[X]) * t0 * v0 ^ 3 -
    (27394048 : F[X]) * t0 * v0 ^ 2 * s0 -
    (19261440 : F[X]) * t0 ^ 3 * v0 ^ 2 * h -
    (18022400 : F[X]) * t0 * u0 ^ 2 * h -
    (16777216 : F[X]) * s0 * a3 * h ^ 4 -
    (14680064 : F[X]) * w0 * a4 * h ^ 2 -
    (10485760 : F[X]) * v0 * b5 * h ^ 2 -
    (8388608 : F[X]) * t0 * b4 * h ^ 5 -
    (6848512 : F[X]) * t0 ^ 3 * b6 * h -
    (6741504 : F[X]) * t0 ^ 5 * s0 * h ^ 2 -
    (3244032 : F[X]) * u0 ^ 2 * Polynomial.C lambda * h ^ 2 -
    (2106720 : F[X]) * t0 ^ 5 * v0 * h ^ 2 -
    (1802240 : F[X]) * t0 ^ 2 * a3 * h ^ 5 -
    (1698543 : F[X]) * t0 ^ 6 * Polynomial.C lambda * h ^ 4 +
    (1203840 : F[X]) * t0 ^ 4 * u0 * h ^ 2 +
    (2568192 : F[X]) * v0 ^ 3 * Polynomial.C lambda * h +
    (4718592 : F[X]) * a2 * Polynomial.C lambda * h ^ 8 +
    (5242880 : F[X]) * t0 * a2 * h ^ 7 +
    (6741504 : F[X]) * t0 ^ 4 * w0 * h ^ 2 +
    (7208960 : F[X]) * t0 ^ 2 * b5 * h ^ 3 +
    (17301504 : F[X]) * t0 * v0 * b6 +
    (23068672 : F[X]) * v0 * u0 * s0 +
    (28835840 : F[X]) * v0 * a3 * h ^ 4 +
    (28835840 : F[X]) * u0 * a4 * h ^ 2 -
    (36044800 : F[X]) * t0 * v0 * a4 * h ^ 2 -
    (27394048 : F[X]) * t0 ^ 2 * u0 * s0 * h -
    (23969792 : F[X]) * t0 ^ 2 * v0 * w0 * h -
    (13001472 : F[X]) * t0 ^ 2 * v0 ^ 2 * Polynomial.C lambda * h ^ 2 -
    (8667648 : F[X]) * t0 ^ 3 * u0 * Polynomial.C lambda * h ^ 3 -
    (6488064 : F[X]) * t0 * a3 * Polynomial.C lambda * h ^ 6 -
    (6488064 : F[X]) * v0 * a4 * Polynomial.C lambda * h ^ 3 +
    (7704576 : F[X]) * t0 ^ 2 * a4 * Polynomial.C lambda * h ^ 4 +
    (9480240 : F[X]) * t0 ^ 4 * v0 * Polynomial.C lambda * h ^ 3 +
    (20185088 : F[X]) * t0 * u0 * w0 * h +
    (23068672 : F[X]) * t0 * s0 * a4 * h ^ 2 +
    (30818304 : F[X]) * t0 ^ 3 * v0 * s0 * h +
    (38522880 : F[X]) * t0 ^ 2 * v0 * u0 * h +
    (15409152 : F[X]) * t0 * v0 * u0 * Polynomial.C lambda * h ^ 2

theorem localClearedSecondDefect810_of_sixthJet
    (h t0 v0 s0 : F[X]) (lambda : F) :
    localClearedSecondDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h ^ 5 * s0)
        lambda =
      h ^ 11 * secondJetParen810 h t0 v0 s0 lambda := by
  simp only [localClearedSecondDefect810, secondJetParen810]
  ring

theorem localClearedThirdDefect810_of_sixthJet
    (h t0 v0 s0 w0 u0 : F[X]) (lambda : F) :
    localClearedThirdDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0)
        (h ^ 5 * s0) (h ^ 3 * w0) lambda =
      h ^ 17 * thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda := by
  simp only [localClearedThirdDefect810, thirdJetParen810_sixth]
  ring

theorem localClearedFourthDefect810_of_sixthJet
    (h t0 v0 s0 w0 u0 a4 b6 : F[X]) (lambda : F) :
    localClearedFourthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0) a4
        (h ^ 5 * s0) (h ^ 3 * w0) b6 lambda =
      h ^ 22 * fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda := by
  simp only [localClearedFourthDefect810, fourthJetParen810_sixth]
  ring

theorem localClearedFifthDefect810_of_sixthJet
    (h t0 v0 s0 w0 u0 a4 a3 b6 b5 : F[X]) (lambda : F) :
    localClearedFifthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0) a4 a3
        (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 lambda =
      h ^ 28 * fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5
        lambda := by
  simp only [localClearedFifthDefect810, fifthJetParen810_sixth]
  ring

set_option maxHeartbeats 8000000 in
theorem localClearedSeventhDefect810_of_sixthJet
    (h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 : F[X]) (lambda : F) :
    localClearedSeventhDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0) a4
        a3 a2 a1 (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 b4 b3 lambda =
      h ^ 39 * seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4
        b3 lambda := by
  simp only [localClearedSeventhDefect810, seventhJetParen810]
  ring

theorem eval_secondJetParen810
    (h t0 v0 s0 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root (secondJetParen810 h t0 v0 s0 lambda) =
      (32 : F) * Polynomial.eval root s0 -
        (40 : F) * Polynomial.eval root v0 := by
  simp [secondJetParen810, hroot]

theorem eval_thirdJetParen810_sixth
    (h t0 v0 s0 w0 u0 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (thirdJetParen810_sixth h t0 v0 s0 w0 u0 lambda) =
      -(512 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 +
        (480 : F) * Polynomial.eval root t0 * Polynomial.eval root v0 -
        (640 : F) * Polynomial.eval root u0 +
        (512 : F) * Polynomial.eval root w0 := by
  simp [thirdJetParen810_sixth, hroot]

theorem eval_fourthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 b6 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (fourthJetParen810_sixth h t0 v0 s0 w0 u0 a4 b6 lambda) =
      (2048 : F) * Polynomial.eval root b6 -
        (2048 : F) * Polynomial.eval root s0 * Polynomial.eval root v0 +
        (2240 : F) * (Polynomial.eval root v0) ^ 2 := by
  simp [fourthJetParen810_sixth, hroot]

theorem eval_fifthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 a3 b6 b5 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (fifthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 b6 b5 lambda) =
      -(98304 : F) * Polynomial.eval root b6 * Polynomial.eval root t0 +
        (212992 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 *
          Polynomial.eval root v0 -
        (131072 : F) * Polynomial.eval root s0 * Polynomial.eval root u0 -
        (199680 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 2 +
        (266240 : F) * Polynomial.eval root u0 * Polynomial.eval root v0 -
        (114688 : F) * Polynomial.eval root v0 *
          Polynomial.eval root w0 := by
  simp [fifthJetParen810_sixth, hroot]

theorem eval_seventhJetParen810
    (h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (seventhJetParen810 h t0 v0 s0 w0 u0 a4 a3 a2 a1 b6 b5 b4 b3
          lambda) =
      (17301504 : F) * Polynomial.eval root b6 * Polynomial.eval root t0 *
          Polynomial.eval root v0 -
        (12582912 : F) * Polynomial.eval root b6 * Polynomial.eval root u0 -
        (27394048 : F) * Polynomial.eval root s0 * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 2 +
        (23068672 : F) * Polynomial.eval root s0 * Polynomial.eval root u0 *
          Polynomial.eval root v0 +
        (25681920 : F) * Polynomial.eval root t0 *
          (Polynomial.eval root v0) ^ 3 -
        (34242560 : F) * Polynomial.eval root u0 *
          (Polynomial.eval root v0) ^ 2 +
        (10092544 : F) * (Polynomial.eval root v0) ^ 2 *
          Polynomial.eval root w0 := by
  simp [seventhJetParen810, hroot]
  ring

/-- The sixth-face jet reduces the second through fifth and seventh
defects to a finite scalar system.  That system splits into the
`v₀ = 0` component `h⁴ ∣ p₆`, `h⁶ ∣ q₈`, `h ∣ q₆` with
`4 w₀ = 5 u₀`, or the `t₀ = 0` component `h⁷ ∣ p₇`, `h² ∣ p₅`,
`h⁴ ∣ q₇` with `4 s₀ = 5 v₀` and `32 b₆ = 5 v₀²`. -/
theorem seventhFace_rootScalars_split810
    (t0 v0 u0 s0 w0 b6 : F)
    (hM : (32 : F) * s0 - (40 : F) * v0 = 0)
    (hT : -(512 : F) * s0 * t0 + (480 : F) * t0 * v0 -
      (640 : F) * u0 + (512 : F) * w0 = 0)
    (hG : (2048 : F) * b6 - (2048 : F) * s0 * v0 +
      (2240 : F) * v0 ^ 2 = 0)
    (hV : -(98304 : F) * b6 * t0 + (212992 : F) * s0 * t0 * v0 -
      (131072 : F) * s0 * u0 - (199680 : F) * t0 * v0 ^ 2 +
      (266240 : F) * u0 * v0 - (114688 : F) * v0 * w0 = 0)
    (hX : (17301504 : F) * b6 * t0 * v0 - (12582912 : F) * b6 * u0 -
      (27394048 : F) * s0 * t0 * v0 ^ 2 +
      (23068672 : F) * s0 * u0 * v0 + (25681920 : F) * t0 * v0 ^ 3 -
      (34242560 : F) * u0 * v0 ^ 2 +
      (10092544 : F) * v0 ^ 2 * w0 = 0) :
    (v0 = 0 ∧ s0 = 0 ∧ b6 = 0 ∧ (4 : F) * w0 = (5 : F) * u0) ∨
      (t0 = 0 ∧ u0 = 0 ∧ w0 = 0 ∧ (4 : F) * s0 = (5 : F) * v0 ∧
        (32 : F) * b6 = (5 : F) * v0 ^ 2) := by
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hsrel : (4 : F) * s0 - (5 : F) * v0 = 0 := by
    have hcomb : (8 : F) * ((4 : F) * s0 - (5 : F) * v0) = 0 := by
      linear_combination hM
    exact (mul_eq_zero.mp hcomb).resolve_left h8
  have hs0 : s0 = (5 / 4 : F) * v0 := by
    field_simp [h4]
    linear_combination hsrel
  have hbrel : (32 : F) * b6 - (5 : F) * v0 ^ 2 = 0 := by
    have hcomb :
        (64 : F) * ((32 : F) * b6 - (5 : F) * v0 ^ 2) = 0 := by
      linear_combination hG + (512 : F) * v0 * hsrel
    exact (mul_eq_zero.mp hcomb).resolve_left h64
  have hb6 : b6 = (5 / 32 : F) * v0 ^ 2 := by
    field_simp [h32]
    linear_combination hbrel
  have hT' : (5 : F) * t0 * v0 + (20 : F) * u0 - (16 : F) * w0 = 0 := by
    linear_combination (-1 / 32 : F) * hT + (-(4 : F) * t0) * hsrel
  have hVsubst :
      -(98304 : F) * ((5 / 32 : F) * v0 ^ 2) * t0 +
          (212992 : F) * ((5 / 4 : F) * v0) * t0 * v0 -
          (131072 : F) * ((5 / 4 : F) * v0) * u0 -
          (199680 : F) * t0 * v0 ^ 2 + (266240 : F) * u0 * v0 -
          (114688 : F) * v0 * w0 = 0 := by
    simpa [hs0, hb6] using hV
  have hV' :
      v0 * ((25 : F) * t0 * v0 + (50 : F) * u0 - (56 : F) * w0) = 0 := by
    have h2048 : (2048 : F) ≠ 0 := by norm_num
    have hscale :
        (2048 : F) *
            (v0 * ((25 : F) * t0 * v0 + (50 : F) * u0 - (56 : F) * w0)) -
          (-(98304 : F) * ((5 / 32 : F) * v0 ^ 2) * t0 +
              (212992 : F) * ((5 / 4 : F) * v0) * t0 * v0 -
              (131072 : F) * ((5 / 4 : F) * v0) * u0 -
              (199680 : F) * t0 * v0 ^ 2 + (266240 : F) * u0 * v0 -
              (114688 : F) * v0 * w0) = 0 := by
      field_simp [h4, h32]
      ring
    have hcomb :
        (2048 : F) *
            (v0 * ((25 : F) * t0 * v0 + (50 : F) * u0 - (56 : F) * w0)) =
          0 := by
      linear_combination hscale + hVsubst
    exact (mul_eq_zero.mp hcomb).resolve_left h2048
  have hXsubst :
      (17301504 : F) * ((5 / 32 : F) * v0 ^ 2) * t0 * v0 -
          (12582912 : F) * ((5 / 32 : F) * v0 ^ 2) * u0 -
          (27394048 : F) * ((5 / 4 : F) * v0) * t0 * v0 ^ 2 +
          (23068672 : F) * ((5 / 4 : F) * v0) * u0 * v0 +
          (25681920 : F) * t0 * v0 ^ 3 -
          (34242560 : F) * u0 * v0 ^ 2 +
          (10092544 : F) * v0 ^ 2 * w0 = 0 := by
    simpa [hs0, hb6] using hX
  have hX' :
      v0 ^ 2 * ((715 : F) * t0 * v0 + (900 : F) * u0 - (1232 : F) * w0) =
        0 := by
    have h8192 : (8192 : F) ≠ 0 := by norm_num
    have hscale :
        -(8192 : F) * v0 ^ 2 *
            ((715 : F) * t0 * v0 + (900 : F) * u0 - (1232 : F) * w0) -
          ((17301504 : F) * ((5 / 32 : F) * v0 ^ 2) * t0 * v0 -
              (12582912 : F) * ((5 / 32 : F) * v0 ^ 2) * u0 -
              (27394048 : F) * ((5 / 4 : F) * v0) * t0 * v0 ^ 2 +
              (23068672 : F) * ((5 / 4 : F) * v0) * u0 * v0 +
              (25681920 : F) * t0 * v0 ^ 3 -
              (34242560 : F) * u0 * v0 ^ 2 +
              (10092544 : F) * v0 ^ 2 * w0) = 0 := by
      field_simp [h4, h32]
      ring
    have hcomb :
        -(8192 : F) * v0 ^ 2 *
            ((715 : F) * t0 * v0 + (900 : F) * u0 - (1232 : F) * w0) =
          0 := by
      linear_combination hscale + hXsubst
    have hpos :
        (8192 : F) *
            (v0 ^ 2 *
              ((715 : F) * t0 * v0 + (900 : F) * u0 - (1232 : F) * w0)) =
          0 := by
      linear_combination -hcomb
    exact (mul_eq_zero.mp hpos).resolve_left h8192
  rcases mul_eq_zero.mp hV' with hv0 | hVface
  · have hs00 : s0 = 0 := by simp [hs0, hv0]
    have hb00 : b6 = 0 := by simp [hb6, hv0]
    have hw : (4 : F) * w0 = (5 : F) * u0 := by
      have hT0 : (20 : F) * u0 - (16 : F) * w0 = 0 := by
        simpa [hv0] using hT'
      have : (4 : F) * ((5 : F) * u0 - (4 : F) * w0) = 0 := by
        linear_combination hT0
      have hrel := (mul_eq_zero.mp this).resolve_left h4
      have : (4 : F) * w0 - (5 : F) * u0 = 0 := by
        linear_combination -hrel
      exact sub_eq_zero.mp this
    exact Or.inl ⟨hv0, hs00, hb00, hw⟩
  · rcases mul_eq_zero.mp hX' with hv2 | hXface
    · have hv0 : v0 = 0 := by
        have hsq : v0 * v0 = 0 := by
          simpa [pow_two] using hv2
        rcases mul_eq_zero.mp hsq with h | h <;> exact h
      have hs00 : s0 = 0 := by simp [hs0, hv0]
      have hb00 : b6 = 0 := by simp [hb6, hv0]
      have hw : (4 : F) * w0 = (5 : F) * u0 := by
        have hT0 : (20 : F) * u0 - (16 : F) * w0 = 0 := by
          simpa [hv0] using hT'
        have : (4 : F) * ((5 : F) * u0 - (4 : F) * w0) = 0 := by
          linear_combination hT0
        have hrel := (mul_eq_zero.mp this).resolve_left h4
        have : (4 : F) * w0 - (5 : F) * u0 = 0 := by
          linear_combination -hrel
        exact sub_eq_zero.mp this
      exact Or.inl ⟨hv0, hs00, hb00, hw⟩
    · have hTV :
          (10 : F) * ((25 : F) * u0 - (12 : F) * w0) = 0 := by
        linear_combination (-(5 : F)) * hVface + (25 : F) * hT'
      have h10 : (10 : F) ≠ 0 := by norm_num
      have huw : (25 : F) * u0 - (12 : F) * w0 = 0 :=
        (mul_eq_zero.mp hTV).resolve_left h10
      have hTX :
          (8 : F) * ((245 : F) * u0 - (132 : F) * w0) = 0 := by
        linear_combination (-(1 : F)) * hXface + (143 : F) * hT'
      have huw2 : (245 : F) * u0 - (132 : F) * w0 = 0 :=
        (mul_eq_zero.mp hTX).resolve_left h8
      have hw0 : w0 = 0 := by
        have hcomb : (72 : F) * w0 = 0 := by
          linear_combination (49 : F) * huw + (-(5 : F)) * huw2
        have h72 : (72 : F) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp hcomb).resolve_left h72
      have hu0 : u0 = 0 := by
        have : (25 : F) * u0 = 0 := by
          simpa [hw0] using huw
        have h25 : (25 : F) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp this).resolve_left h25
      have hx0 : t0 * v0 = 0 := by
        have : (5 : F) * (t0 * v0) = 0 := by
          simpa [hu0, hw0] using hT'
        have h5 : (5 : F) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp this).resolve_left h5
      rcases mul_eq_zero.mp hx0 with ht0 | hv0
      · exact Or.inr ⟨ht0, hu0, hw0, sub_eq_zero.mp hsrel,
          sub_eq_zero.mp hbrel⟩
      · have hs00 : s0 = 0 := by simp [hs0, hv0]
        have hb00 : b6 = 0 := by simp [hb6, hv0]
        have hw : (4 : F) * w0 = (5 : F) * u0 := by
          simp [hw0, hu0]
        exact Or.inl ⟨hv0, hs00, hb00, hw⟩

end SeventhFaceScalars810

/-! ## Source-facing seventh-face packet -/

section NonzeroSeventhFace810

variable {k : Type*} [Field k] [CharZero k]

/-- The sixth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁴⁹`. -/
theorem nonzeroFace810_seventhDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          lambda =
        Polynomial.C eta * h0 ^ 49 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
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
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
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
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
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
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 5) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 5) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
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
  have hf1 : f.coeff 1 =
      depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedF810, a7, a6, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedOctic68_one]
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
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow12)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 3) hLconst halpha0 hbeta0 hgamma0 hdelta0
      (by simpa using hrow10)
  obtain ⟨eta0, heta0⟩ :
      ∃ a : k,
        zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
            (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hzeta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda) =
        (16777216 : RatFunc k) * h ^ 49 *
          zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
            (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) := by
    have hF := seventhDefect_eq_clearedZeta810 h a7 a6 a5 a4 a3 a2 a1 b9
      b8 b7 b6 b5 b4 b3 (RatFunc.C lambda) hh (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedSeventhDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, h, a7, a6, a5, a4, a3, a2,
      a1, b8, b7, b6, b5, b4, b3, zetaResidual810, alphaResidual810,
      betaResidual810, gammaResidual810, deltaResidual810, hf6, hf5, hf4,
      hf3, hf2, hf1, hg3, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (16777216 * eta0) * h0 ^ 49) := by
    rw [hclear, heta0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨16777216 * eta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Source-facing seventh integral for a normalized scale-two `(8,10)`
nonzero face. -/
theorem normalized810ScaleTwo_nonzeroFace_seventhDefectPowerRelation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda eta : K),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        localClearedSeventhDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) lambda =
          Polynomial.C eta * h0 ^ 49 := by
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
  obtain ⟨eta, hXrel⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8' hq10' hN' hD
  exact ⟨h0, lambda, eta, hh0, hlambda, hh0degree, hH, hN', hXrel⟩

end NonzeroSeventhFace810

#print axioms seventhCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_10_monicOcticDecic
#print axioms seventhDefect_eq_clearedZeta810
#print axioms zetaResidual810_deriv_zero
#print axioms seventhFace_rootScalars_split810
#print axioms nonzeroFace810_seventhDefectPowerRelation
#print axioms normalized810ScaleTwo_nonzeroFace_seventhDefectPowerRelation

end Max11DegreeRoutes
