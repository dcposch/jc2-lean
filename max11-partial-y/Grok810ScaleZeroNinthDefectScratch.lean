import Grok810ScaleZeroEighthDefectScratch

/-! # Scale-zero ninth defect for the normalized `(8,10)`, `H = 0` leaf

The eighth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first eight octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, and `h⁶³`.  This file consumes the next
unused Keller coefficient of the same monic octic-decic depression: the
degree-`7` Jacobian row is
`8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 8 X' = 0`.  The
corresponding tenth cleared polynomial defect of weight seventy is
likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`70` defect itself.  Root-evaluation from a scale-two
tenth face is unavailable, because a nonzero constant has no finite
root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`6` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the eighth-defect
packet start at degree `7`. -/
theorem grokScaleZero_tenthCoefficientJacobianRow_raw_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 4).derivative +
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
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
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
  rw [hC8, hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

section Depression810TenthClearing

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁰` coefficient. -/
def depressedX810 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- First residual of the degree-`7` row. -/
def iotaResidual810
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0 : F) : F :=
  X0 - (alphaResidual810 A P * G0 +
    (7 / 8 : F) * betaResidual810 L A B Q * F0 +
    (3 / 4 : F) * gammaResidual810 L A B C0 P R * E0 +
    (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * D0 +
    (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * C0 +
    (3 / 8 : F) * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 * B +
    (1 / 4 : F) * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 * A +
    (5 / 16 : F) * A * G0 + (5 / 16 : F) * B * F0 +
    (5 / 16 : F) * C0 * E0 + (5 / 32 : F) * D0 ^ 2 -
    (15 / 128 : F) * A ^ 2 * E0 - (15 / 64 : F) * A * B * D0 -
    (15 / 128 : F) * A * C0 ^ 2 - (15 / 128 : F) * B ^ 2 * C0 +
    (35 / 512 : F) * A ^ 3 * C0 + (105 / 1024 : F) * A ^ 2 * B ^ 2 -
    (77 / 8192 : F) * A ^ 5 +
    (9 / 64 : F) * L * A * F0 + (9 / 64 : F) * L * B * E0 +
    (9 / 64 : F) * L * C0 * D0 - (63 / 1024 : F) * L * A ^ 2 * D0 -
    (63 / 512 : F) * L * A * B * C0 - (21 / 1024 : F) * L * B ^ 3 +
    (315 / 8192 : F) * L * A ^ 3 * B +
    (5 / 128 : F) * gammaResidual810 L A B C0 P R * A ^ 3 -
    (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * C0 -
    (3 / 32 : F) * gammaResidual810 L A B C0 P R * B ^ 2 +
    (63 / 1024 : F) * betaResidual810 L A B Q * A ^ 2 * B -
    (7 / 64 : F) * betaResidual810 L A B Q * A * D0 -
    (7 / 64 : F) * betaResidual810 L A B Q * B * C0 -
    (1 / 8 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A ^ 2 -
    (15 / 64 : F) * deltaResidual810 L A B C0 D0 P Q S0 * A * B)

set_option maxHeartbeats 4000000 in
/-- Polynomial numerator of `32 h⁷⁰ ι` on the ninth-power face. -/
def localClearedTenthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F[X])
    (lambda : F) : F[X] :=
  - (1 : F[X]) * a7 ^ 10
    + (4 : F[X]) * h ^ 6 * a7 ^ 8 * b8
    + (1 : F[X]) * h ^ 7 * a7 ^ 9 * Polynomial.C lambda
    + (5 : F[X]) * h ^ 8 * a7 ^ 8 * a6
    - (32 : F[X]) * h ^ 14 * a7 ^ 6 * a6 * b8
    - (4 : F[X]) * h ^ 14 * a7 ^ 7 * b7
    - (9 : F[X]) * h ^ 15 * a7 ^ 7 * a6 * Polynomial.C lambda
    + (5 : F[X]) * h ^ 16 * a7 ^ 6 * a6 ^ 2
    - (5 : F[X]) * h ^ 16 * a7 ^ 7 * a5
    + (80 : F[X]) * h ^ 22 * a7 ^ 4 * a6 ^ 2 * b8
    + (32 : F[X]) * h ^ 22 * a7 ^ 5 * a5 * b8
    + (28 : F[X]) * h ^ 22 * a7 ^ 5 * a6 * b7
    + (4 : F[X]) * h ^ 22 * a7 ^ 6 * b6
    + (27 : F[X]) * h ^ 23 * a7 ^ 5 * a6 ^ 2 * Polynomial.C lambda
    + (9 : F[X]) * h ^ 23 * a7 ^ 6 * a5 * Polynomial.C lambda
    - (50 : F[X]) * h ^ 24 * a7 ^ 4 * a6 ^ 3
    - (15 : F[X]) * h ^ 24 * a7 ^ 5 * a6 * a5
    + (5 : F[X]) * h ^ 24 * a7 ^ 6 * a4
    - (64 : F[X]) * h ^ 30 * a7 ^ 2 * a6 ^ 3 * b8
    - (128 : F[X]) * h ^ 30 * a7 ^ 3 * a6 * a5 * b8
    - (56 : F[X]) * h ^ 30 * a7 ^ 3 * a6 ^ 2 * b7
    - (32 : F[X]) * h ^ 30 * a7 ^ 4 * a4 * b8
    - (28 : F[X]) * h ^ 30 * a7 ^ 4 * a5 * b7
    - (24 : F[X]) * h ^ 30 * a7 ^ 4 * a6 * b6
    - (4 : F[X]) * h ^ 30 * a7 ^ 5 * b5
    - (30 : F[X]) * h ^ 31 * a7 ^ 3 * a6 ^ 3 * Polynomial.C lambda
    - (45 : F[X]) * h ^ 31 * a7 ^ 4 * a6 * a5 * Polynomial.C lambda
    - (9 : F[X]) * h ^ 31 * a7 ^ 5 * a4 * Polynomial.C lambda
    + (55 : F[X]) * h ^ 32 * a7 ^ 2 * a6 ^ 4
    + (130 : F[X]) * h ^ 32 * a7 ^ 3 * a6 ^ 2 * a5
    + (10 : F[X]) * h ^ 32 * a7 ^ 4 * a5 ^ 2
    + (20 : F[X]) * h ^ 32 * a7 ^ 4 * a6 * a4
    - (5 : F[X]) * h ^ 32 * a7 ^ 5 * a3
    + (8 : F[X]) * h ^ 38 * a6 ^ 4 * b8
    + (96 : F[X]) * h ^ 38 * a7 * a6 ^ 2 * a5 * b8
    + (28 : F[X]) * h ^ 38 * a7 * a6 ^ 3 * b7
    + (48 : F[X]) * h ^ 38 * a7 ^ 2 * a5 ^ 2 * b8
    + (96 : F[X]) * h ^ 38 * a7 ^ 2 * a6 * a4 * b8
    + (84 : F[X]) * h ^ 38 * a7 ^ 2 * a6 * a5 * b7
    + (36 : F[X]) * h ^ 38 * a7 ^ 2 * a6 ^ 2 * b6
    + (32 : F[X]) * h ^ 38 * a7 ^ 3 * a3 * b8
    + (28 : F[X]) * h ^ 38 * a7 ^ 3 * a4 * b7
    + (24 : F[X]) * h ^ 38 * a7 ^ 3 * a5 * b6
    + (20 : F[X]) * h ^ 38 * a7 ^ 3 * a6 * b5
    + (4 : F[X]) * h ^ 38 * a7 ^ 4 * b4
    + (9 : F[X]) * h ^ 39 * a7 * a6 ^ 4 * Polynomial.C lambda
    + (54 : F[X]) * h ^ 39 * a7 ^ 2 * a6 ^ 2 * a5 * Polynomial.C lambda
    + (18 : F[X]) * h ^ 39 * a7 ^ 3 * a5 ^ 2 * Polynomial.C lambda
    + (36 : F[X]) * h ^ 39 * a7 ^ 3 * a6 * a4 * Polynomial.C lambda
    + (9 : F[X]) * h ^ 39 * a7 ^ 4 * a3 * Polynomial.C lambda
    - (8 : F[X]) * h ^ 40 * a6 ^ 5
    - (115 : F[X]) * h ^ 40 * a7 * a6 ^ 3 * a5
    - (105 : F[X]) * h ^ 40 * a7 ^ 2 * a6 * a5 ^ 2
    - (105 : F[X]) * h ^ 40 * a7 ^ 2 * a6 ^ 2 * a4
    - (25 : F[X]) * h ^ 40 * a7 ^ 3 * a5 * a4
    - (25 : F[X]) * h ^ 40 * a7 ^ 3 * a6 * a3
    + (5 : F[X]) * h ^ 40 * a7 ^ 4 * a2
    - (32 : F[X]) * h ^ 46 * a6 * a5 ^ 2 * b8
    - (32 : F[X]) * h ^ 46 * a6 ^ 2 * a4 * b8
    - (28 : F[X]) * h ^ 46 * a6 ^ 2 * a5 * b7
    - (8 : F[X]) * h ^ 46 * a6 ^ 3 * b6
    - (64 : F[X]) * h ^ 46 * a7 * a5 * a4 * b8
    - (28 : F[X]) * h ^ 46 * a7 * a5 ^ 2 * b7
    - (64 : F[X]) * h ^ 46 * a7 * a6 * a3 * b8
    - (56 : F[X]) * h ^ 46 * a7 * a6 * a4 * b7
    - (48 : F[X]) * h ^ 46 * a7 * a6 * a5 * b6
    - (20 : F[X]) * h ^ 46 * a7 * a6 ^ 2 * b5
    - (32 : F[X]) * h ^ 46 * a7 ^ 2 * a2 * b8
    - (28 : F[X]) * h ^ 46 * a7 ^ 2 * a3 * b7
    - (24 : F[X]) * h ^ 46 * a7 ^ 2 * a4 * b6
    - (20 : F[X]) * h ^ 46 * a7 ^ 2 * a5 * b5
    - (16 : F[X]) * h ^ 46 * a7 ^ 2 * a6 * b4
    - (4 : F[X]) * h ^ 46 * a7 ^ 3 * b3
    - (9 : F[X]) * h ^ 47 * a6 ^ 3 * a5 * Polynomial.C lambda
    - (27 : F[X]) * h ^ 47 * a7 * a6 * a5 ^ 2 * Polynomial.C lambda
    - (27 : F[X]) * h ^ 47 * a7 * a6 ^ 2 * a4 * Polynomial.C lambda
    - (27 : F[X]) * h ^ 47 * a7 ^ 2 * a5 * a4 * Polynomial.C lambda
    - (27 : F[X]) * h ^ 47 * a7 ^ 2 * a6 * a3 * Polynomial.C lambda
    - (9 : F[X]) * h ^ 47 * a7 ^ 3 * a2 * Polynomial.C lambda
    + (60 : F[X]) * h ^ 48 * a6 ^ 2 * a5 ^ 2
    + (40 : F[X]) * h ^ 48 * a6 ^ 3 * a4
    + (25 : F[X]) * h ^ 48 * a7 * a5 ^ 3
    + (150 : F[X]) * h ^ 48 * a7 * a6 * a5 * a4
    + (75 : F[X]) * h ^ 48 * a7 * a6 ^ 2 * a3
    + (15 : F[X]) * h ^ 48 * a7 ^ 2 * a4 ^ 2
    + (30 : F[X]) * h ^ 48 * a7 ^ 2 * a5 * a3
    + (30 : F[X]) * h ^ 48 * a7 ^ 2 * a6 * a2
    - (5 : F[X]) * h ^ 48 * a7 ^ 3 * a1
    + (16 : F[X]) * h ^ 54 * a4 ^ 2 * b8
    + (32 : F[X]) * h ^ 54 * a5 * a3 * b8
    + (28 : F[X]) * h ^ 54 * a5 * a4 * b7
    + (12 : F[X]) * h ^ 54 * a5 ^ 2 * b6
    + (32 : F[X]) * h ^ 54 * a6 * a2 * b8
    + (28 : F[X]) * h ^ 54 * a6 * a3 * b7
    + (24 : F[X]) * h ^ 54 * a6 * a4 * b6
    + (20 : F[X]) * h ^ 54 * a6 * a5 * b5
    + (8 : F[X]) * h ^ 54 * a6 ^ 2 * b4
    + (32 : F[X]) * h ^ 54 * a7 * a1 * b8
    + (28 : F[X]) * h ^ 54 * a7 * a2 * b7
    + (24 : F[X]) * h ^ 54 * a7 * a3 * b6
    + (20 : F[X]) * h ^ 54 * a7 * a4 * b5
    + (16 : F[X]) * h ^ 54 * a7 * a5 * b4
    + (12 : F[X]) * h ^ 54 * a7 * a6 * b3
    + (4 : F[X]) * h ^ 54 * a7 ^ 2 * b2
    + (3 : F[X]) * h ^ 55 * a5 ^ 3 * Polynomial.C lambda
    + (18 : F[X]) * h ^ 55 * a6 * a5 * a4 * Polynomial.C lambda
    + (9 : F[X]) * h ^ 55 * a6 ^ 2 * a3 * Polynomial.C lambda
    + (9 : F[X]) * h ^ 55 * a7 * a4 ^ 2 * Polynomial.C lambda
    + (18 : F[X]) * h ^ 55 * a7 * a5 * a3 * Polynomial.C lambda
    + (18 : F[X]) * h ^ 55 * a7 * a6 * a2 * Polynomial.C lambda
    + (9 : F[X]) * h ^ 55 * a7 ^ 2 * a1 * Polynomial.C lambda
    - (40 : F[X]) * h ^ 56 * a5 ^ 2 * a4
    - (40 : F[X]) * h ^ 56 * a6 * a4 ^ 2
    - (80 : F[X]) * h ^ 56 * a6 * a5 * a3
    - (40 : F[X]) * h ^ 56 * a6 ^ 2 * a2
    - (35 : F[X]) * h ^ 56 * a7 * a4 * a3
    - (35 : F[X]) * h ^ 56 * a7 * a5 * a2
    - (35 : F[X]) * h ^ 56 * a7 * a6 * a1
    + (5 : F[X]) * h ^ 56 * a7 ^ 2 * a0
    + (32 : F[X]) * h ^ 70 * b0
    - (32 : F[X]) * h ^ 62 * a0 * b8
    - (28 : F[X]) * h ^ 62 * a1 * b7
    - (24 : F[X]) * h ^ 62 * a2 * b6
    - (20 : F[X]) * h ^ 62 * a3 * b5
    - (16 : F[X]) * h ^ 62 * a4 * b4
    - (12 : F[X]) * h ^ 62 * a5 * b3
    - (8 : F[X]) * h ^ 62 * a6 * b2
    - (4 : F[X]) * h ^ 62 * a7 * b1
    - (9 : F[X]) * h ^ 63 * a4 * a3 * Polynomial.C lambda
    - (9 : F[X]) * h ^ 63 * a5 * a2 * Polynomial.C lambda
    - (9 : F[X]) * h ^ 63 * a6 * a1 * Polynomial.C lambda
    - (9 : F[X]) * h ^ 63 * a7 * a0 * Polynomial.C lambda
    + (20 : F[X]) * h ^ 64 * a3 ^ 2
    + (40 : F[X]) * h ^ 64 * a4 * a2
    + (40 : F[X]) * h ^ 64 * a5 * a1
    + (40 : F[X]) * h ^ 64 * a6 * a0

/-- Exact denominator clearing for the decic `z⁰` coordinate on the
ninth-power face. -/
theorem depressedX810_eq_cleared
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
        b1 b0 =
      (-9 * a7 ^ 10 + 2 * lambda * a7 ^ 9 * h ^ 7 +
          64 * a7 ^ 8 * b8 * h ^ 6 - 512 * a7 ^ 7 * b7 * h ^ 14 +
          4096 * a7 ^ 6 * b6 * h ^ 22 - 32768 * a7 ^ 5 * b5 * h ^ 30 +
          262144 * a7 ^ 4 * b4 * h ^ 38 - 2097152 * a7 ^ 3 * b3 * h ^ 46 +
          16777216 * a7 ^ 2 * b2 * h ^ 54 - 134217728 * a7 * b1 * h ^ 62 +
          1073741824 * b0 * h ^ 70) /
        (1073741824 * h ^ 70) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h1073741824 : (1073741824 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4pow : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh70 : h ^ 70 ≠ 0 := pow_ne_zero 70 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedX810, octicDepressionR810]
  have hrewrite :
      (a7 / (8 * h ^ 7)) ^ 10 -
          (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 9 +
        (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 8 -
          (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) ^ 7 +
        (b6 / h ^ 6) * (a7 / (8 * h ^ 7)) ^ 6 -
          (b5 / h ^ 5) * (a7 / (8 * h ^ 7)) ^ 5 +
        (b4 / h ^ 4) * (a7 / (8 * h ^ 7)) ^ 4 -
          (b3 / h ^ 3) * (a7 / (8 * h ^ 7)) ^ 3 +
        (b2 / h ^ 2) * (a7 / (8 * h ^ 7)) ^ 2 -
          (b1 / h) * (a7 / (8 * h ^ 7)) + b0 =
        (-9 * a7 ^ 10 + 2 * lambda * a7 ^ 9 * h ^ 7 +
            64 * a7 ^ 8 * b8 * h ^ 6 - 512 * a7 ^ 7 * b7 * h ^ 14 +
            4096 * a7 ^ 6 * b6 * h ^ 22 - 32768 * a7 ^ 5 * b5 * h ^ 30 +
            262144 * a7 ^ 4 * b4 * h ^ 38 -
            2097152 * a7 ^ 3 * b3 * h ^ 46 +
            16777216 * a7 ^ 2 * b2 * h ^ 54 -
            134217728 * a7 * b1 * h ^ 62 + 1073741824 * b0 * h ^ 70) /
          (1073741824 * h ^ 70) := by
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh70, h1073741824]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh70, h1073741824]
    ring
  exact hrewrite

set_option maxHeartbeats 40000000 in
/-- Clearing the first integral
`X - α G - (7/8) β F - (3/4) γ E - (5/8) δ D - (1/2) ε C - (3/8) ζ B
- (1/4) η A - (5/16) A G - (5/16) B F - (5/16) C E - (5/32) D²
+ (15/128) A² E + (15/64) A B D + (15/128) A C² + (15/128) B² C
- (35/512) A³ C - (105/1024) A² B² + (77/8192) A⁵
- (9/64) L A F - (9/64) L B E - (9/64) L C D + (63/1024) L A² D
+ (63/512) L A B C + (21/1024) L B³ - (315/8192) L A³ B
- (5/128) γ A³ + (3/16) γ A C + (3/32) γ B²
- (63/1024) β A² B + (7/64) β A D + (7/64) β B C
+ (1/8) ε A² + (15/64) δ A B`
against `h⁷⁰` on the ninth-power face. -/
theorem tenthDefect_eq_clearedIota810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    (32 : F) * h ^ 70 *
        iotaResidual810
          (depressedL810 h (octicDepressionR810 h a7) b9)
          (depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
          (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
          (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
          (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1)
          (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
            a1 a0)
          (depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
          (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
          (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
          (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3)
          (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2)
          (depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
            b3 b2 b1 b0) =
  - (1 : F) * a7 ^ 10
    + (4 : F) * h ^ 6 * a7 ^ 8 * b8
    + (1 : F) * h ^ 7 * a7 ^ 9 * lambda
    + (5 : F) * h ^ 8 * a7 ^ 8 * a6
    - (32 : F) * h ^ 14 * a7 ^ 6 * a6 * b8
    - (4 : F) * h ^ 14 * a7 ^ 7 * b7
    - (9 : F) * h ^ 15 * a7 ^ 7 * a6 * lambda
    + (5 : F) * h ^ 16 * a7 ^ 6 * a6 ^ 2
    - (5 : F) * h ^ 16 * a7 ^ 7 * a5
    + (80 : F) * h ^ 22 * a7 ^ 4 * a6 ^ 2 * b8
    + (32 : F) * h ^ 22 * a7 ^ 5 * a5 * b8
    + (28 : F) * h ^ 22 * a7 ^ 5 * a6 * b7
    + (4 : F) * h ^ 22 * a7 ^ 6 * b6
    + (27 : F) * h ^ 23 * a7 ^ 5 * a6 ^ 2 * lambda
    + (9 : F) * h ^ 23 * a7 ^ 6 * a5 * lambda
    - (50 : F) * h ^ 24 * a7 ^ 4 * a6 ^ 3
    - (15 : F) * h ^ 24 * a7 ^ 5 * a6 * a5
    + (5 : F) * h ^ 24 * a7 ^ 6 * a4
    - (64 : F) * h ^ 30 * a7 ^ 2 * a6 ^ 3 * b8
    - (128 : F) * h ^ 30 * a7 ^ 3 * a6 * a5 * b8
    - (56 : F) * h ^ 30 * a7 ^ 3 * a6 ^ 2 * b7
    - (32 : F) * h ^ 30 * a7 ^ 4 * a4 * b8
    - (28 : F) * h ^ 30 * a7 ^ 4 * a5 * b7
    - (24 : F) * h ^ 30 * a7 ^ 4 * a6 * b6
    - (4 : F) * h ^ 30 * a7 ^ 5 * b5
    - (30 : F) * h ^ 31 * a7 ^ 3 * a6 ^ 3 * lambda
    - (45 : F) * h ^ 31 * a7 ^ 4 * a6 * a5 * lambda
    - (9 : F) * h ^ 31 * a7 ^ 5 * a4 * lambda
    + (55 : F) * h ^ 32 * a7 ^ 2 * a6 ^ 4
    + (130 : F) * h ^ 32 * a7 ^ 3 * a6 ^ 2 * a5
    + (10 : F) * h ^ 32 * a7 ^ 4 * a5 ^ 2
    + (20 : F) * h ^ 32 * a7 ^ 4 * a6 * a4
    - (5 : F) * h ^ 32 * a7 ^ 5 * a3
    + (8 : F) * h ^ 38 * a6 ^ 4 * b8
    + (96 : F) * h ^ 38 * a7 * a6 ^ 2 * a5 * b8
    + (28 : F) * h ^ 38 * a7 * a6 ^ 3 * b7
    + (48 : F) * h ^ 38 * a7 ^ 2 * a5 ^ 2 * b8
    + (96 : F) * h ^ 38 * a7 ^ 2 * a6 * a4 * b8
    + (84 : F) * h ^ 38 * a7 ^ 2 * a6 * a5 * b7
    + (36 : F) * h ^ 38 * a7 ^ 2 * a6 ^ 2 * b6
    + (32 : F) * h ^ 38 * a7 ^ 3 * a3 * b8
    + (28 : F) * h ^ 38 * a7 ^ 3 * a4 * b7
    + (24 : F) * h ^ 38 * a7 ^ 3 * a5 * b6
    + (20 : F) * h ^ 38 * a7 ^ 3 * a6 * b5
    + (4 : F) * h ^ 38 * a7 ^ 4 * b4
    + (9 : F) * h ^ 39 * a7 * a6 ^ 4 * lambda
    + (54 : F) * h ^ 39 * a7 ^ 2 * a6 ^ 2 * a5 * lambda
    + (18 : F) * h ^ 39 * a7 ^ 3 * a5 ^ 2 * lambda
    + (36 : F) * h ^ 39 * a7 ^ 3 * a6 * a4 * lambda
    + (9 : F) * h ^ 39 * a7 ^ 4 * a3 * lambda
    - (8 : F) * h ^ 40 * a6 ^ 5
    - (115 : F) * h ^ 40 * a7 * a6 ^ 3 * a5
    - (105 : F) * h ^ 40 * a7 ^ 2 * a6 * a5 ^ 2
    - (105 : F) * h ^ 40 * a7 ^ 2 * a6 ^ 2 * a4
    - (25 : F) * h ^ 40 * a7 ^ 3 * a5 * a4
    - (25 : F) * h ^ 40 * a7 ^ 3 * a6 * a3
    + (5 : F) * h ^ 40 * a7 ^ 4 * a2
    - (32 : F) * h ^ 46 * a6 * a5 ^ 2 * b8
    - (32 : F) * h ^ 46 * a6 ^ 2 * a4 * b8
    - (28 : F) * h ^ 46 * a6 ^ 2 * a5 * b7
    - (8 : F) * h ^ 46 * a6 ^ 3 * b6
    - (64 : F) * h ^ 46 * a7 * a5 * a4 * b8
    - (28 : F) * h ^ 46 * a7 * a5 ^ 2 * b7
    - (64 : F) * h ^ 46 * a7 * a6 * a3 * b8
    - (56 : F) * h ^ 46 * a7 * a6 * a4 * b7
    - (48 : F) * h ^ 46 * a7 * a6 * a5 * b6
    - (20 : F) * h ^ 46 * a7 * a6 ^ 2 * b5
    - (32 : F) * h ^ 46 * a7 ^ 2 * a2 * b8
    - (28 : F) * h ^ 46 * a7 ^ 2 * a3 * b7
    - (24 : F) * h ^ 46 * a7 ^ 2 * a4 * b6
    - (20 : F) * h ^ 46 * a7 ^ 2 * a5 * b5
    - (16 : F) * h ^ 46 * a7 ^ 2 * a6 * b4
    - (4 : F) * h ^ 46 * a7 ^ 3 * b3
    - (9 : F) * h ^ 47 * a6 ^ 3 * a5 * lambda
    - (27 : F) * h ^ 47 * a7 * a6 * a5 ^ 2 * lambda
    - (27 : F) * h ^ 47 * a7 * a6 ^ 2 * a4 * lambda
    - (27 : F) * h ^ 47 * a7 ^ 2 * a5 * a4 * lambda
    - (27 : F) * h ^ 47 * a7 ^ 2 * a6 * a3 * lambda
    - (9 : F) * h ^ 47 * a7 ^ 3 * a2 * lambda
    + (60 : F) * h ^ 48 * a6 ^ 2 * a5 ^ 2
    + (40 : F) * h ^ 48 * a6 ^ 3 * a4
    + (25 : F) * h ^ 48 * a7 * a5 ^ 3
    + (150 : F) * h ^ 48 * a7 * a6 * a5 * a4
    + (75 : F) * h ^ 48 * a7 * a6 ^ 2 * a3
    + (15 : F) * h ^ 48 * a7 ^ 2 * a4 ^ 2
    + (30 : F) * h ^ 48 * a7 ^ 2 * a5 * a3
    + (30 : F) * h ^ 48 * a7 ^ 2 * a6 * a2
    - (5 : F) * h ^ 48 * a7 ^ 3 * a1
    + (16 : F) * h ^ 54 * a4 ^ 2 * b8
    + (32 : F) * h ^ 54 * a5 * a3 * b8
    + (28 : F) * h ^ 54 * a5 * a4 * b7
    + (12 : F) * h ^ 54 * a5 ^ 2 * b6
    + (32 : F) * h ^ 54 * a6 * a2 * b8
    + (28 : F) * h ^ 54 * a6 * a3 * b7
    + (24 : F) * h ^ 54 * a6 * a4 * b6
    + (20 : F) * h ^ 54 * a6 * a5 * b5
    + (8 : F) * h ^ 54 * a6 ^ 2 * b4
    + (32 : F) * h ^ 54 * a7 * a1 * b8
    + (28 : F) * h ^ 54 * a7 * a2 * b7
    + (24 : F) * h ^ 54 * a7 * a3 * b6
    + (20 : F) * h ^ 54 * a7 * a4 * b5
    + (16 : F) * h ^ 54 * a7 * a5 * b4
    + (12 : F) * h ^ 54 * a7 * a6 * b3
    + (4 : F) * h ^ 54 * a7 ^ 2 * b2
    + (3 : F) * h ^ 55 * a5 ^ 3 * lambda
    + (18 : F) * h ^ 55 * a6 * a5 * a4 * lambda
    + (9 : F) * h ^ 55 * a6 ^ 2 * a3 * lambda
    + (9 : F) * h ^ 55 * a7 * a4 ^ 2 * lambda
    + (18 : F) * h ^ 55 * a7 * a5 * a3 * lambda
    + (18 : F) * h ^ 55 * a7 * a6 * a2 * lambda
    + (9 : F) * h ^ 55 * a7 ^ 2 * a1 * lambda
    - (40 : F) * h ^ 56 * a5 ^ 2 * a4
    - (40 : F) * h ^ 56 * a6 * a4 ^ 2
    - (80 : F) * h ^ 56 * a6 * a5 * a3
    - (40 : F) * h ^ 56 * a6 ^ 2 * a2
    - (35 : F) * h ^ 56 * a7 * a4 * a3
    - (35 : F) * h ^ 56 * a7 * a5 * a2
    - (35 : F) * h ^ 56 * a7 * a6 * a1
    + (5 : F) * h ^ 56 * a7 ^ 2 * a0
    + (32 : F) * h ^ 70 * b0
    - (32 : F) * h ^ 62 * a0 * b8
    - (28 : F) * h ^ 62 * a1 * b7
    - (24 : F) * h ^ 62 * a2 * b6
    - (20 : F) * h ^ 62 * a3 * b5
    - (16 : F) * h ^ 62 * a4 * b4
    - (12 : F) * h ^ 62 * a5 * b3
    - (8 : F) * h ^ 62 * a6 * b2
    - (4 : F) * h ^ 62 * a7 * b1
    - (9 : F) * h ^ 63 * a4 * a3 * lambda
    - (9 : F) * h ^ 63 * a5 * a2 * lambda
    - (9 : F) * h ^ 63 * a6 * a1 * lambda
    - (9 : F) * h ^ 63 * a7 * a0 * lambda
    + (20 : F) * h ^ 64 * a3 ^ 2
    + (40 : F) * h ^ 64 * a4 * a2
    + (40 : F) * h ^ 64 * a5 * a1
    + (40 : F) * h ^ 64 * a6 * a0 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h1073741824 : (1073741824 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  have hh70 : h ^ 70 ≠ 0 := pow_ne_zero 70 hh
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
  have hG0 :
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
          a0 =
        (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
            262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
            4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
            64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
          (16777216 * h ^ 56) :=
    depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh
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
  have hT0 :
      depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 =
        (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
            2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
            30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
            131072 * b4 * h ^ 38) /
          (131072 * h ^ 42) :=
    depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hU0 :
      depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 =
        (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
            448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
            10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
            131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
          (262144 * h ^ 49) :=
    depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
  have hV0 :
      depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 -
            6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) :=
    depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hX0 :
      depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 b0 =
        (-9 * a7 ^ 10 + 2 * lambda * a7 ^ 9 * h ^ 7 +
            64 * a7 ^ 8 * b8 * h ^ 6 - 512 * a7 ^ 7 * b7 * h ^ 14 +
            4096 * a7 ^ 6 * b6 * h ^ 22 - 32768 * a7 ^ 5 * b5 * h ^ 30 +
            262144 * a7 ^ 4 * b4 * h ^ 38 -
            2097152 * a7 ^ 3 * b3 * h ^ 46 +
            16777216 * a7 ^ 2 * b2 * h ^ 54 -
            134217728 * a7 * b1 * h ^ 62 + 1073741824 * b0 * h ^ 70) /
          (1073741824 * h ^ 70) :=
    depressedX810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda hh
      hN
  simp only [iotaResidual810, hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ,
    hR, hS, hT0, hU0, hV0, hX0, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h128, h512, h1024, h2048,
    h8192, h32768, h65536, h131072, h262144, h16777216, h67108864,
    h1073741824, hh14, hh21, hh28, hh35, hh42, hh49, hh56, hh63, hh70]
  ring

end Depression810TenthClearing

/-! ## Degree-`7` depressed Jacobian coefficient -/

section DepressedRow810Tenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`7` Jacobian coefficient is
exactly `8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 8 X'`. -/
theorem differentialJacobian_coeff_7_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 7 =
      (8 : F) * g.coeff 8 * d (f.coeff 0) +
        (7 : F) * g.coeff 7 * d (f.coeff 1) +
        (6 : F) * g.coeff 6 * d (f.coeff 2) +
        (5 : F) * g.coeff 5 * d (f.coeff 3) +
        (4 : F) * g.coeff 4 * d (f.coeff 4) +
        (3 : F) * g.coeff 3 * d (f.coeff 5) +
        (2 : F) * g.coeff 2 * d (f.coeff 6) -
          f.coeff 1 * d (g.coeff 7) -
          (2 : F) * f.coeff 2 * d (g.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 5) -
          (4 : F) * f.coeff 4 * d (g.coeff 4) -
          (5 : F) * f.coeff 5 * d (g.coeff 3) -
          (6 : F) * f.coeff 6 * d (g.coeff 2) -
          (8 : F) * d (g.coeff 0) := by
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
  have hmem07 : ((0, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem16 : ((1, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem25 : ((2, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem34 : ((3, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem43 : ((4, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem52 : ((5, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem61 : ((6, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem70 : ((7, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 7 =
        (8 : F) * g.coeff 8 * d (f.coeff 0) +
          (7 : F) * g.coeff 7 * d (f.coeff 1) +
          (6 : F) * g.coeff 6 * d (f.coeff 2) +
          (5 : F) * g.coeff 5 * d (f.coeff 3) +
          (4 : F) * g.coeff 4 * d (f.coeff 4) +
          (3 : F) * g.coeff 3 * d (f.coeff 5) +
          (2 : F) * g.coeff 2 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne07_16 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne07_25 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne07_34 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne07_43 : ((0, 7) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne07_52 : ((0, 7) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne07_61 : ((0, 7) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne16_25 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne16_34 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne16_43 : ((1, 6) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne16_52 : ((1, 6) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne16_61 : ((1, 6) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne25_34 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne25_43 : ((2, 5) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne25_52 : ((2, 5) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne25_61 : ((2, 5) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne34_43 : ((3, 4) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne34_52 : ((3, 4) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne34_61 : ((3, 4) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne43_52 : ((4, 3) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne43_61 : ((4, 3) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hne52_61 : ((5, 2) : ℕ × ℕ) ≠ (6, 1) := by decide
    have hsubset :
        ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb | hb
      · subst b; exact hmem07
      · subst b; exact hmem16
      · subst b; exact hmem25
      · subst b; exact hmem34
      · subst b; exact hmem43
      · subst b; exact hmem52
      · subst b; exact hmem61
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
              (6, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne62 : b ≠ (6, 1) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0; apply hne08; ext; exact h0; omega
        have hne1 : b.1 ≠ 1 := by
          intro h1; apply hne17; ext; exact h1; omega
        have hne2 : b.1 ≠ 2 := by
          intro h2; apply hne26; ext; exact h2; omega
        have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne35; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne44; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne53; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne62; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
            (6, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 1 := by
      rw [Finset.sum_insert (by simp [hne07_16, hne07_25, hne07_34, hne07_43,
            hne07_52, hne07_61]),
        Finset.sum_insert (by simp [hne16_25, hne16_34, hne16_43, hne16_52,
            hne16_61]),
        Finset.sum_insert (by simp [hne25_34, hne25_43, hne25_52, hne25_61]),
        Finset.sum_insert (by simp [hne34_43, hne34_52, hne34_61]),
        Finset.sum_insert (by simp [hne43_52, hne43_61]),
        Finset.sum_insert (by simp [hne52_61]), Finset.sum_singleton]
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
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder7, hder6, hder5,
      hder4, hder3, hder2, hder1g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 7 =
        f.coeff 1 * d (g.coeff 7) +
          (2 : F) * f.coeff 2 * d (g.coeff 6) +
          (3 : F) * f.coeff 3 * d (g.coeff 5) +
          (4 : F) * f.coeff 4 * d (g.coeff 4) +
          (5 : F) * f.coeff 5 * d (g.coeff 3) +
          (6 : F) * f.coeff 6 * d (g.coeff 2) +
          (8 : F) * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul]
    have hne07_16 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne07_25 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne07_34 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne07_43 : ((0, 7) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne07_52 : ((0, 7) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne07_70 : ((0, 7) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne16_25 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne16_34 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne16_43 : ((1, 6) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne16_52 : ((1, 6) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne16_70 : ((1, 6) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne25_34 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne25_43 : ((2, 5) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne25_52 : ((2, 5) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne25_70 : ((2, 5) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne34_43 : ((3, 4) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne34_52 : ((3, 4) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne34_70 : ((3, 4) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne43_52 : ((4, 3) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne43_70 : ((4, 3) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hne52_70 : ((5, 2) : ℕ × ℕ) ≠ (7, 0) := by decide
    have hsubset :
        ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (7, 0)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb | hb
      · subst b; exact hmem07
      · subst b; exact hmem16
      · subst b; exact hmem25
      · subst b; exact hmem34
      · subst b; exact hmem43
      · subst b; exact hmem52
      · subst b; exact hmem70
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
              (7, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne71 : b ≠ (7, 0) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · have hne0 : b.1 ≠ 0 := by
            intro h0; apply hne08; ext; exact h0; omega
          have hne1 : b.1 ≠ 1 := by
            intro h1; apply hne17; ext; exact h1; omega
          have hne2 : b.1 ≠ 2 := by
            intro h2; apply hne26; ext; exact h2; omega
          have hne3 : b.1 ≠ 3 := by
            intro h3; apply hne35; ext; exact h3; omega
          have hne4 : b.1 ≠ 4 := by
            intro h4; apply hne44; ext; exact h4; omega
          have hne5 : b.1 ≠ 5 := by
            intro h5; apply hne53; ext; exact h5; omega
          have hne7 : b.1 ≠ 7 := by
            intro h7; apply hne71; ext; exact h7; omega
          have hj : 9 ≤ b.2 := by omega
          simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2),
            (7, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne07_16, hne07_25, hne07_34, hne07_43,
            hne07_52, hne07_70]),
        Finset.sum_insert (by simp [hne16_25, hne16_34, hne16_43, hne16_52,
            hne16_70]),
        Finset.sum_insert (by simp [hne25_34, hne25_43, hne25_52, hne25_70]),
        Finset.sum_insert (by simp [hne34_43, hne34_52, hne34_70]),
        Finset.sum_insert (by simp [hne43_52, hne43_70]),
        Finset.sum_insert (by simp [hne52_70]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
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
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder0, hder1, hder2,
      hder3, hder4, hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 40000000 in
theorem iotaResidual810_deriv_zero
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (hrow : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0) :
    d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0 := by
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
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h315 : d (315 : F) = 0 := d.map_natCast 315
  have h512 : d (512 : F) = 0 := d.map_natCast 512
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h32768 : d (32768 : F) = 0 := d.map_natCast 32768
  have h77 : d (77 : F) = 0 := d.map_natCast 77
  have h105 : d (105 : F) = 0 := d.map_natCast 105
  have h8192 : d (8192 : F) = 0 := d.map_natCast 8192
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have h18 : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
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
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h15128 : d (15 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h15]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h7128 : d (7 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h7]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have h1564 : d (15 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h15]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h7]
  have h35512 : d (35 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h35]
  have h211024 : d (21 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h21]
  have h631024 : d (63 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h63]
  have h31532768 : d (315 / 32768 : F) = 0 := by
    simp [Derivation.leibniz_div, h32768, h315]
  have h778192 : d (77 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h77]
  have h3158192 : d (315 / 8192 : F) = 0 := by
    simp [Derivation.leibniz_div, h8192, h315]
  have h1051024 : d (105 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h105]
  have h63512 : d (63 / 512 : F) = 0 := by
    simp [Derivation.leibniz_div, h512, h63]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h3]
  have h352048 : d (35 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h35]
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
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz]
    ring
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + alphaResidual810 A P * d A) := by
    simp only [gammaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h532, hL, halpha, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hRderiv' :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + alphaResidual810 A P * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    rw [hRderiv']
    simp only [alphaResidual810]
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          alphaResidual810 A P * d B +
          (7 / 8 : F) * betaResidual810 L A B Q * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    unfold deltaResidual810
    simp [map_sub, map_add, Derivation.leibniz, h54, h98, h78, h516, h964,
      h9128, hL, halpha, hbeta, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hSderiv' :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        alphaResidual810 A P * d B +
        (7 / 8 : F) * betaResidual810 L A B Q * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    rw [hSderiv']
    simp [alphaResidual810, betaResidual810]
  have hepsilon_id :
      d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) =
        d T0 - ((5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
          (5 / 16 : F) * (A * d C0 + C0 * d A) -
          (15 / 128 : F) * A ^ 2 * d A +
          L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
          alphaResidual810 A P * d C0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d B +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A) := by
    simp only [epsilonResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h532, h516, h5128, h15128, h964, hL, halpha, hbeta,
      hgamma, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
    ring
  have hTderiv' :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        alphaResidual810 A P * d C0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d B +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A := by
    linear_combination hepsilon_id.symm + hepsilon
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        (P - (5 / 4 : F) * A) * d C0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d B +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d A := by
    rw [hTderiv']
    simp [gammaResidual810, alphaResidual810, betaResidual810]
  have hzeta_id :
      d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) =
        d U0 - ((5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
          alphaResidual810 A P * d D0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
          (5 / 16 : F) * (A * d D0 + D0 * d A) +
          (5 / 16 : F) * (B * d C0 + C0 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
          (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
          (63 / 1024 : F) * L * A ^ 2 * d A +
          (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
          (9 / 64 : F) * L * B * d B) := by
    simp only [zetaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h58, h516, h7128, h15128, h211024, h964, h9128, hL,
      halpha, hbeta, hgamma, hdelta, zero_mul, add_zero, mul_zero, pow_two,
      hsq, hsqB, hcub]
    ring
  have hUderiv' :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        alphaResidual810 A P * d D0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d C0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d B +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * A * d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    linear_combination hzeta_id.symm + hzeta
  have hUderiv :
      d U0 = (5 / 4 : F) * d F0 + (9 / 8 : F) * L * d E0 +
        (P - (5 / 4 : F) * A) * d D0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d C0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d B +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d A +
        (5 / 16 : F) * (A * d D0 + D0 * d A) +
        (5 / 16 : F) * (B * d C0 + C0 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A *
          d A -
        (15 / 128 : F) * (2 * A * B * d A + A ^ 2 * d B) -
        (63 / 1024 : F) * L * A ^ 2 * d A +
        (9 / 64 : F) * L * (A * d C0 + C0 * d A) +
        (9 / 64 : F) * L * B * d B := by
    rw [hUderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810]
  have heta_id :
      d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) =
        d V0 - ((5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
          alphaResidual810 A P * d E0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
          (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
          (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
          (5 / 16 : F) * (A * d E0 + E0 * d A) +
          (5 / 16 : F) * (B * d D0 + D0 * d B) +
          (5 / 16 : F) * C0 * d C0 -
          (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
          (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
          (35 / 512 : F) * A ^ 3 * d A +
          (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
          (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
          (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
          (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
          (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A) := by
    simp only [etaResidual810, map_sub, map_add, Derivation.leibniz, h12,
      h14, h18, h54, h98, h78, h34, h58, h516, h532, h15128, h352048, h964,
      h631024, h764, h332, hL, halpha, hbeta, hgamma, hdelta, hepsilon,
      zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hsqC, hcub, hquar]
    ring
  have hVderiv' :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        alphaResidual810 A P * d E0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d D0 +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d C0 +
        (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * d B +
        (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * betaResidual810 L A B Q * (A * d B + B * d A) -
        (3 / 16 : F) * gammaResidual810 L A B C0 P R * A * d A := by
    linear_combination heta_id.symm + heta
  have hVderiv :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        (P - (5 / 4 : F) * A) * d E0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d D0 +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d C0 +
        (5 / 8 : F) * (S0 - ((5 / 4 : F) * D0 + (9 / 8 : F) * L * C0 +
          (P - (5 / 4 : F) * A) * B +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * A +
          (5 / 16 : F) * A * B + (9 / 128 : F) * L * A ^ 2)) * d B +
        (1 / 2 : F) * (T0 - ((5 / 4 : F) * E0 + (5 / 32 : F) * B ^ 2 +
          (5 / 16 : F) * A * C0 - (5 / 128 : F) * A ^ 3 +
          L * ((9 / 8 : F) * D0 + (9 / 64 : F) * A * B) +
          (P - (5 / 4 : F) * A) * C0 +
          (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * B +
          (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
            (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A)) * d A +
        (5 / 16 : F) * (A * d E0 + E0 * d A) +
        (5 / 16 : F) * (B * d D0 + D0 * d B) +
        (5 / 16 : F) * C0 * d C0 -
        (15 / 128 : F) * (B ^ 2 * d A + (2 : F) * A * B * d B) -
        (15 / 128 : F) * ((2 : F) * A * C0 * d A + A ^ 2 * d C0) +
        (35 / 512 : F) * A ^ 3 * d A +
        (9 / 64 : F) * L * (B * d C0 + C0 * d B) +
        (9 / 64 : F) * L * (A * d D0 + D0 * d A) -
        (63 / 1024 : F) * L * ((2 : F) * A * B * d A + A ^ 2 * d B) -
        (7 / 64 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) *
          (A * d B + B * d A) -
        (3 / 16 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * A * d A := by
    rw [hVderiv']
    simp [alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810]
  have hXderiv :
      d X0 = P * d G0 + (7 / 8 : F) * Q * d F0 +
        (3 / 4 : F) * R * d E0 + (5 / 8 : F) * S0 * d D0 +
        (1 / 2 : F) * T0 * d C0 + (3 / 8 : F) * U0 * d B +
        (1 / 4 : F) * V0 * d A -
        (1 / 8 : F) * F0 * d Q - (1 / 4 : F) * E0 * d R -
        (3 / 8 : F) * D0 * d S0 - (1 / 2 : F) * C0 * d T0 -
        (5 / 8 : F) * B * d U0 - (3 / 4 : F) * A * d V0 := by
    linear_combination (-1 / 8 : F) * hrow
  simp only [iotaResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810,
    zetaResidual810, etaResidual810, map_sub, map_add, Derivation.leibniz,
    h12, h14, h18, h38, h54, h98, h78, h34, h58, h516, h316, h532, h15128,
    h5128, h7128, h9128, h1564, h964, h764, h35512, h211024, h631024,
    h31532768, h778192, h3158192, h1051024, h63512, h332, h352048, hL,
    zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hsqC, hsqD, hcub,
    hcubB, hquar, hquint]
  rw [hXderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv, hVderiv]
  ring

end DepressedRow810Tenth


/-! ## Affine depression of a degree-ten source, `z⁰` coefficient -/

section AffineDecic810Tenth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁰` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff0_810
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 0 =
      r ^ 10 - (p.coeff 9 / h ^ 9) * r ^ 9 +
        (p.coeff 8 / h ^ 8) * r ^ 8 -
        (p.coeff 7 / h ^ 7) * r ^ 7 +
        (p.coeff 6 / h ^ 6) * r ^ 6 -
        (p.coeff 5 / h ^ 5) * r ^ 5 +
        (p.coeff 4 / h ^ 4) * r ^ 4 -
        (p.coeff 3 / h ^ 3) * r ^ 3 +
        (p.coeff 2 / h ^ 2) * r ^ 2 -
        (p.coeff 1 / h) * r + p.coeff 0 := by
  let plow : (RatFunc k)[X] :=
    p - Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 - Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 -
      Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 - Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 -
      Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 - Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 -
      Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 - Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 -
      Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 - Polynomial.C (p.coeff 1) * Polynomial.X ^ 1
  have hplow : ∀ n, 1 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h1 | hlt1
    · subst n; simp
    · have : 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h2 | hlt2
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
                          show n ≠ 3 by omega, show n ≠ 2 by omega,
                          show n ≠ 1 by omega]
  have hplowDeg : plow.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 + Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 +
        Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 + Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 +
        Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 + Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 +
        Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 + Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 +
        Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X ^ 1 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := rfl
    have hsum (A B D E G H I J K M s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + M + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + M.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + M + s).comp t =
          (A + B + D + E + G + H + I + J + K + M).comp t + s.comp t :=
        Polynomial.add_comp
      have h2 : (A + B + D + E + G + H + I + J + K + M).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + M.comp t :=
        Polynomial.add_comp
      have h3 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t :=
        Polynomial.add_comp
      have h4 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t :=
        Polynomial.add_comp
      have h5 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t :=
        Polynomial.add_comp
      have h6 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := Polynomial.add_comp
      have h7 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := Polynomial.add_comp
      have h8 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := Polynomial.add_comp
      have h9 : (A + B + D).comp t =
          (A + B).comp t + D.comp t := Polynomial.add_comp
      have h10 : (A + B).comp t = A.comp t + B.comp t := Polynomial.add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    exact hdef.trans ((congrArg (fun t => t.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _ _))
  have hlow0 :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        p.coeff 0 := by
    have hC : plow = Polynomial.C (plow.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hplowDeg
    have hcoeff0 : plow.coeff 0 = p.coeff 0 := by
      simp [plow]
    rw [hC, Polynomial.C_comp, Polynomial.coeff_C, if_pos rfl, hcoeff0]
  have h10_0 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        r ^ 10 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 0 hh]
    have hle : (0 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hp10, hbin, pow_zero]
    field_simp [hh]; ring
  have h9_0 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 9 / h ^ 9) * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 0 hh]
    have hle : (0 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h8_0 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 8 / h ^ 8) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 0 hh]
    have hle : (0 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h7_0 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 7 / h ^ 7) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 0 hh]
    have hle : (0 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h6_0 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 6 / h ^ 6) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 0 hh]
    have hle : (0 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h5_0 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 5 / h ^ 5) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 0 hh]
    have hle : (0 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h4_0 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 4 / h ^ 4) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 0 hh]
    have hle : (0 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h3_0 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 3 / h ^ 3) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 0 hh]
    have hle : (0 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_three]
    field_simp [hh]; ring
  have h2_0 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 2 / h ^ 2) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 0 hh]
    have hle : (0 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_two]
    field_simp [hh]; ring
  have h1_0 :
      ((Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 1 / h) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 0 hh]
    have hle : (0 : ℕ) ≤ 1 := by omega
    have hbin : (1 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_one]
    field_simp [hh]; ring
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, h10_0, h9_0, h8_0, h7_0, h6_0, h5_0, h4_0, h3_0,
    h2_0, h1_0, hlow0]
  ring

end AffineDecic810Tenth

section NonzeroTenthFaceClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The ninth octic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁷⁰`. -/
theorem nonzeroFace810_tenthDefectPowerRelation
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
      localClearedTenthDefect810 h0 (p.coeff 7) (p.coeff 6) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C eta * h0 ^ 70 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let a6 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 6)
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
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
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
  have hg4 :
      g.coeff 4 =
        depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedT810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedV810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4
          b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedU810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedW810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg0 :
      g.coeff 0 =
        depressedX810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3
          b2 b1 b0 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff0_810 (sourceToRatFunc68 q) h
      (octicDepressionR810 h a7) hh hgTop hg_high_src]
    simp [depressedX810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
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
    have hx := ratFuncDerivation46_polynomial (Polynomial.C (-lambda / 4) : k[X])
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
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 5) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 4) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
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
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 5) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 3) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 5) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 6) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (5 : RatFunc k) * f.coeff 5 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * f.coeff 6 * ratFuncDerivation68 (g.coeff 2) -
          (8 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicOcticDecic
        ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
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
  have hf0 : f.coeff 0 =
      depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedG810, a7, a6, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedOctic68_zero]
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
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow11)
  have hzeta0 :
      ratFuncDerivation68
        (zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
      (g.coeff 3) hLconst halpha0 hbeta0 hgamma0 hdelta0
      (by simpa using hrow10)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 2)) = 0 :=
    etaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0 hbeta0
      hgamma0 hdelta0 hepsilon0 (by simpa using hrow9)
  have hiota0deriv :
      ratFuncDerivation68
        (iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual810_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
      (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
      (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0deriv
      (by simpa using hrow7)
  obtain ⟨iota0, hiota0⟩ :
      ∃ a : k,
        iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 0) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hiota0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedTenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda) =
        (32 : RatFunc k) * h ^ 70 *
          iotaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 0) := by
    have hF := tenthDefect_eq_clearedIota810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 b0 (RatFunc.C lambda) hh (by convert hNrat)
    have hg9L : g.coeff 9 =
        depressedL810 h (octicDepressionR810 h a7) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
        sourceToRatFunc46, b9]
    simpa [localClearedTenthDefect810, map_sub, map_mul, map_pow,
      map_ofNat, map_neg, map_add, RatFunc.algebraMap_C, h, a7, a6, a5,
      a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, b0, iotaResidual810,
      alphaResidual810, betaResidual810, gammaResidual810,
      deltaResidual810, epsilonResidual810, zetaResidual810, etaResidual810, hf6, hf5, hf4, hf3, hf2, hf1,
      hf0, hg0, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedTenthDefect810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
            (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
            (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (32 * iota0) * h0 ^ 70) := by
    rw [hclear, hiota0]
    simp [h, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨32 * iota0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroTenthFaceClearing810

section ScaleZeroNinthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Degree-`7` source Jacobian row -/

/-- Source-facing degree-`7` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_tenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using grokScaleZero_tenthCoefficientJacobianRow_raw_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`7` row is a differential constant. -/
theorem scaleZero_tenthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) =
      0 := by
  have hrow := grokScaleZero_tenthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow

/-- Source-facing scale-zero collapse of the degree-`7` row. -/
theorem normalized810ScaleZero_tenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 7).derivative * q.coeff 1 +
        (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 0).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 1).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        p.coeff 1 * (q.coeff 7).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_tenthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`7` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`7` Jacobian coefficient
is exactly
`8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 8 X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree7Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 7 =
      (8 : F) * g.coeff 8 * d (f.coeff 0) +
        (7 : F) * g.coeff 7 * d (f.coeff 1) +
        (6 : F) * g.coeff 6 * d (f.coeff 2) +
        (5 : F) * g.coeff 5 * d (f.coeff 3) +
        (4 : F) * g.coeff 4 * d (f.coeff 4) +
        (3 : F) * g.coeff 3 * d (f.coeff 5) +
        (2 : F) * g.coeff 2 * d (f.coeff 6) -
          f.coeff 1 * d (g.coeff 7) -
          (2 : F) * f.coeff 2 * d (g.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 5) -
          (4 : F) * f.coeff 4 * d (g.coeff 4) -
          (5 : F) * f.coeff 5 * d (g.coeff 3) -
          (6 : F) * f.coeff 6 * d (g.coeff 2) -
          (8 : F) * d (g.coeff 0) :=
  differentialJacobian_coeff_7_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if
`8 P G' + 7 Q F' + 6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 8 X' = 0`,
`L` is constant, and the second through eighth residuals
`α, β, γ, δ, ε, ζ, η` are constant, then the first residual `ι` is a
differential constant. -/
theorem scaleZero_iotaResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (hrow : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0) :
    d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0 :=
  iotaResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta hrow

/-! ## Cleared weight-`70` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_ninthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda eta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_tenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

/-- Aligned constant face `N = 0`: the same degree-`7` clearing applies
with `λ = 0`, and the weight-`70` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedNinthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedTenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_tenthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`70` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroNinthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (_hlambda : lambda ≠ 0)
    (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9) :
    ∃ eta : k,
      localClearedTenthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_tenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

/-- Source-facing ninth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`70`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_ninthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, eta, hN, hX⟩ :=
    scaleZero_ninthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

/-- The weight-`70` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_ninthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, eta, ht, hHsq, _hN, hX⟩ :=
    normalized810ScaleZero_exists_ninthClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 70, ht, hHsq, ?_⟩
  have hconst :
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C (eta * t ^ 70) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 70)).symm
  exact hconst

/-- Newton degree of the ninth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_ninthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_ninthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Aligned/nonzero split of the scale-zero ninth defect: both constant
faces of `N` make the weight-`70` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_ninthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedTenthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
                (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 70) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedTenthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 70) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_ninthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`70` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_ninthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
      let X :=
        localClearedTenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (q.coeff 0)
          lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, eta0, ht, hHsq, hN, hXpow⟩ :=
    normalized810ScaleZero_exists_ninthClearedDefect hsource
  let eta : k := eta0 * t ^ 70
  have hX :
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 70)).symm
  refine ⟨t, lambda, eta, ht, hHsq, hN, hX, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
                  H -
              (4 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
            Polynomial.C (lambda * t ^ 9) := by
        rw [hN, ← Polynomial.C_pow]
        exact (map_mul (Polynomial.C : k →+* k[X]) lambda (t ^ 9)).symm
      exact hNconst
  · by_cases heta : eta = 0
    · left
      refine ⟨heta, ?_⟩
      simpa only [heta, Polynomial.C_0] using hX
    · exact Or.inr ⟨heta, hX⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`70` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_ninthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          0 =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨eta, hX⟩ :=
    scaleZero_alignedNinthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`70` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_ninthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 70 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_ninthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroNinthDefect810


#print axioms grokScaleZero_tenthCoefficientJacobianRow_raw_810
#print axioms scaleZero_tenthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_tenthCoefficientJacobianRow
#print axioms normalized810ScaleZero_tenthCoefficientJacobianRow_collapsed
#print axioms scaleZero_monicOcticDecic_degree7Row_810
#print axioms scaleZero_iotaResidual_deriv_zero_810
#print axioms affineDepress_degreeTen_coeff0_810
#print axioms tenthDefect_eq_clearedIota810
#print axioms nonzeroFace810_tenthDefectPowerRelation
#print axioms scaleZero_ninthClearedDefect_exists_C_810
#print axioms scaleZero_alignedNinthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroNinthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_ninthClearedDefect
#print axioms normalized810ScaleZero_ninthClearedDefect_exists_C
#print axioms normalized810ScaleZero_ninthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_ninthClearedDefectFirstFace
#print axioms normalized810ScaleZero_ninthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_ninthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_ninthClearedDefect

end Max11DegreeRoutes
