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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- Depressed decic `z⁰` coefficient. -/
def depressedX810 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

set_option maxHeartbeats 64000000 in
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

-- Fix the polynomial carrier while preserving the complete literal definition.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
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


-- Materialize the existing definition equation in its owning module.
#print axioms localClearedTenthDefect810.eq_1

end Depression810TenthClearing

end Max11DegreeRoutes
end
