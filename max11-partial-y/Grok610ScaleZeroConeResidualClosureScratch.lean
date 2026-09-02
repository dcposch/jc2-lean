import Grok610ScaleZeroConeCascadeScratch

/-! # Scale-zero cone residual closure for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeCascadeScratch` on the constant core
`H = (C t)²`.  That file closed a constant core, the unique-`A` cone
except the leftover chambers `L = 0` with `B` constant (and `β = 0` if
`B = 0`), the extreme unique-`B` cone `3 deg A < 2 deg B`, a unique
nonconstant `B` or `D₀`, and a unique nonconstant `E₀` with `β ≠ 0`.

This file continues the same Newton-degree / unique-face comparison of
the weight-fifteen primitive against derivative `C (j / t) ≠ 0`.  CAS
enumeration of the leftover cones (`derive_610_scale_zero_cone_residual.py`)
identifies the following unique faces, which this file closes.

* Unique-`A`, `L = 0`, `deg B = 0`, combined `A⁶` coefficient
  `(-(62720/2239488)) B + C (2695/559872 β)` nonzero: the face `A⁶`
  has degree `6 deg A ≥ 6`.  This includes the subchamber `β = 0`
  with `B` a nonzero constant.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀` nonconstant: the face
  `A⁵ D₀` has degree `5 deg A + deg D₀ ≥ 6`.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀` constant, combined `A⁵`
  coefficient `(92160/2239488) D₀ + C (49/5184 δ)` nonzero: the face
  `A⁵` has degree `5 deg A ≥ 5`.
* Unique-`A`, `L = 0`, `B = 0`, `β = 0`, `D₀ = 0`, `δ = 0`: the
  remaining primitive is `ζ` times a quartic in `(A, C₀)` plus `θ`
  times a cubic in `(A, C₀, E₀)`.  Nonzero `ζ` makes `A⁴` unique of
  degree `≥ 4`; vanishing `ζ` and nonzero `θ` makes `A³` unique of
  degree `≥ 3`; vanishing both makes the primitive constant.
* Unique nonconstant `C₀` with cubic coefficient
  `(419904/2239488 L) A + (414720/2239488) B - C (36288/559872 β)`
  nonzero: the face `C₀³` has degree `3 deg C₀ ≥ 3`.
* Unique nonconstant `E₀` with `β = 0` and `deg E₀ ≥ 2`: the primitive
  is affine in `E₀`, so either the linear coefficient is a nonzero
  constant and the degree equals `deg E₀ ≥ 2`, or the linear
  coefficient vanishes and the primitive is constant.
* Unique-`B` with `2 deg B < 3 deg A`: the face `A⁶ B` has degree
  `6 deg A + deg B > 5 deg B`.  Combined with the parent extreme cone
  `3 deg A < 2 deg B` (which forces `7 deg A < 5 deg B` over
  `ℕ`), the only leftover unique-`B` chamber is the tie `3 deg A = 2 deg B`.
* `A, B, C₀` constant, `β = 0`, `D₀` nonconstant, `deg E₀ < 2 deg D₀`:
  the face `D₀³` has degree `3 deg D₀`, strictly above `D₀²`, `D₀ E₀`,
  and `E₀`.

The leaf is not closed.  Named remaining cones are recorded by
`normalized610ScaleZero_coneResidualClosureResidual`.  No total-degree
or twice-prime theorem is used.  No finite-root shortcut is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Additional cones -/

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `C₀` cone. -/
def UniqueHighC0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    A.natDegree < C0.natDegree ∧
    B.natDegree < C0.natDegree ∧
    D0.natDegree < C0.natDegree ∧
    E0.natDegree < C0.natDegree

/-- Unique-max `D₀` cone. -/
def UniqueHighD0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    A.natDegree < D0.natDegree ∧
    B.natDegree < D0.natDegree ∧
    C0.natDegree < D0.natDegree ∧
    E0.natDegree < D0.natDegree

/-- Unique-max `E₀` cone. -/
def UniqueHighE0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree < E0.natDegree ∧
    B.natDegree < E0.natDegree ∧
    C0.natDegree < E0.natDegree ∧
    D0.natDegree < E0.natDegree

/-- Unique-`B` subcone on which `A⁶ B` strictly outranks `B⁵`. -/
def A6BLeadsHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    2 * B.natDegree < 3 * A.natDegree

/-- Combined `A⁶` coefficient on the unique-`A` chamber `L = 0`,
`deg B = 0`. -/
def highA_l0_constB_A6Coefficient610 (beta : k) (B : k[X]) : k[X] :=
  (-(62720 / 2239488 : k)) • B + C (2695 / 559872 * beta : k)

/-- Combined `A⁵` coefficient on the unique-`A` chamber `L = 0`,
`B = 0`, `β = 0`, `D₀` constant. -/
def highA_l0_B0_beta0_A5Coefficient610 (delta : k) (D0 : k[X]) : k[X] :=
  (92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)

/-- Combined `C₀³` coefficient on a unique-nonconstant `C₀` chamber. -/
def uniqueC0_cubicCoefficient610 (l beta : k) (A B : k[X]) : k[X] :=
  (419904 / 2239488 * l : k) • A +
    (414720 / 2239488 : k) • B +
    C (-(36288 / 559872 * beta : k))

end ExtraCones610

/-! ## Primitive splittings for the leftover unique faces -/

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive with the face `A⁶ B` deleted, `A⁷` retained. -/
def degreeZeroPrimitiveNoA6B610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 +
    degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0

/-- Primitive at `L = 0` with both `A⁶ B` and `β A⁶` deleted. -/
def degreeZeroPrimitiveHighA_l0_noA6_Rest610
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Base group at `L = 0`, `B = 0` with `A⁵ D₀` deleted. -/
def degreeZeroBaseGroup_l0_B0_noA5D0_Rest610
    (A C0 D0 E0 : k[X]) : k[X] :=
  (-(668160 / 2239488 : k)) • (A ^ 3 * C0 * D0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Delta group with the face `A⁵` deleted. -/
def degreeZeroDeltaGroupNoA5Polynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(360 / 5184 : k)) • (A ^ 3 * C0) -
    (600 / 5184 : k) • (A ^ 2 * B ^ 2) +
    (1440 / 5184 : k) • (A * B * D0) +
    (720 / 5184 : k) • (A * C0 ^ 2) +
    (720 / 5184 : k) • (B ^ 2 * C0) -
    (2160 / 5184 : k) • D0 ^ 2

/-- Primitive at `L = 0`, `B = 0`, `β = 0` with `A⁵ D₀` deleted. -/
def degreeZeroPrimitive_l0_B0_beta0_noA5D0_Rest610
    (alpha delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroup_l0_B0_noA5D0_Rest610 A C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A 0 C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A 0 C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A 0 C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A 0 C0 E0

/-- Primitive at `L = 0`, `B = 0`, `β = 0` with both `A⁵ D₀` and `δ A⁵`
deleted. -/
def degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610
    (alpha delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroup_l0_B0_noA5D0_Rest610 A C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0 +
    delta • degreeZeroDeltaGroupNoA5Polynomial610 A 0 C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A 0 C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A 0 C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A 0 C0 E0

/-- Primitive at `L = 0`, `B = 0`, `D₀ = 0`, `β = 0`.  The letters
`α, ε, η` drop out. -/
def degreeZeroPrimitive_l0_B0_D00_beta0_610
    (delta zeta theta : k) (A C0 E0 : k[X]) : k[X] :=
  (49 / 5184 * delta : k) • A ^ 5 -
    (360 / 5184 * delta : k) • (A ^ 3 * C0) +
    (720 / 5184 * delta : k) • (A * C0 ^ 2) -
    (7 / 192 * zeta : k) • A ^ 4 +
    (40 / 192 * zeta : k) • (A ^ 2 * C0) -
    (48 / 192 * zeta : k) • C0 ^ 2 +
    (7 / 216 * theta : k) • A ^ 3 -
    (36 / 216 * theta : k) • (A * C0) +
    theta • E0

/-- Linear `E₀` coefficient of the primitive at `β = 0`. -/
def degreeZeroE0LinearPolynomial610
    (l alpha theta : k) (A B C0 D0 : k[X]) : k[X] :=
  (-(122472 / 2239488 * l : k)) • A ^ 4 -
    (483840 / 2239488 : k) • (A ^ 3 * B) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2) +
    (1658880 / 2239488 : k) • (A * B * C0) +
    (276480 / 2239488 : k) • B ^ 3 -
    (1679616 / 2239488 * l : k) • (B * D0) -
    (839808 / 2239488 * l : k) • C0 ^ 2 -
    (2488320 / 2239488 : k) • (C0 * D0) +
    (189 / 729 * alpha : k) • (A ^ 2 * B) -
    (324 / 729 * alpha : k) • (A * D0) -
    (324 / 729 * alpha : k) • (B * C0) +
    C theta

/-- The `E₀`-linear summands of the primitive at `β = 0`, written as
scalar multiples of monomials times `E₀`. -/
def degreeZeroE0Terms610
    (l alpha theta : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(122472 / 2239488 * l : k)) • (A ^ 4 * E0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) +
    (189 / 729 * alpha : k) • (A ^ 2 * B * E0) -
    (324 / 729 * alpha : k) • (A * D0 * E0) -
    (324 / 729 * alpha : k) • (B * C0 * E0) +
    theta • E0

/-- Base group with the three `C₀³` faces deleted. -/
def degreeZeroBaseGroupNoC03Polynomial610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 -
    (62720 / 2239488 : k) • (A ^ 6 * B) +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Beta group with the face `C₀³` deleted. -/
def degreeZeroBetaGroupNoC03Polynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (2695 / 559872 : k) • A ^ 6 -
    (23940 / 559872 : k) • (A ^ 4 * C0) -
    (51660 / 559872 : k) • (A ^ 3 * B ^ 2) +
    (21168 / 559872 : k) • (A ^ 3 * E0) +
    (127008 / 559872 : k) • (A ^ 2 * B * D0) +
    (63504 / 559872 : k) • (A ^ 2 * C0 ^ 2) +
    (136080 / 559872 : k) • (A * B ^ 2 * C0) -
    (108864 / 559872 : k) • (A * C0 * E0) -
    (108864 / 559872 : k) • (A * D0 ^ 2) +
    (11340 / 559872 : k) • B ^ 4 -
    (54432 / 559872 : k) • (B ^ 2 * E0) -
    (217728 / 559872 : k) • (B * C0 * D0) +
    (326592 / 559872 : k) • E0 ^ 2

/-- Primitive with the three `C₀³` faces deleted. -/
def degreeZeroPrimitiveNoC03Rest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupNoC03Polynomial610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupNoC03Polynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitiveHighARest610_eq_A6B_add_noA6B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitiveHighARest610,
    degreeZeroPrimitiveHighA_noA6B_Rest610,
    degreeZeroBaseGroupHighARest610,
    degreeZeroBaseGroupHighA_noA6B_Rest610]
  module

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A6B_add_noA6B_withA7
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        degreeZeroPrimitiveNoA6B610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    degreeZeroPrimitiveHighARest610_eq_A6B_add_noA6B]
  simp only [degreeZeroPrimitiveNoA6B610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A6_combined_add_rest
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        ((2695 / 559872 * beta : k) • A ^ 6) +
          degreeZeroPrimitiveHighA_l0_noA6_Rest610 alpha beta delta
            epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighA_l0_noA6_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighA_noA6B_Rest610,
    degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero, neg_zero,
    zero_smul, smul_zero, zero_add, add_zero, sub_zero]
  module

theorem highA_l0_constB_A6_combined_eq
    (beta : k) (A B : k[X]) :
    (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        ((2695 / 559872 * beta : k) • A ^ 6) =
      A ^ 6 * highA_l0_constB_A6Coefficient610 beta B := by
  simp only [highA_l0_constB_A6Coefficient610, smul_eq_C_mul]
  ring

private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A5D0_add_rest
    (alpha delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta eta
        theta A 0 C0 D0 E0 =
      (92160 / 2239488 : k) • (A ^ 5 * D0) +
        degreeZeroPrimitive_l0_B0_beta0_noA5D0_Rest610 alpha delta
          epsilon zeta eta theta A C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitive_l0_B0_beta0_noA5D0_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroup_l0_B0_noA5D0_Rest610, zero_mul, mul_zero,
    neg_zero, zero_smul, smul_zero, zero_add, add_zero, sub_zero,
    zero_pow_two, zero_pow_three, zero_pow_four, zero_pow_five]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_A5_combined_add_rest
    (alpha delta epsilon zeta eta theta : k)
    (A C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta eta
        theta A 0 C0 D0 E0 =
      (92160 / 2239488 : k) • (A ^ 5 * D0) +
        ((49 / 5184 * delta : k) • A ^ 5) +
          degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610 alpha delta
            epsilon zeta eta theta A C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610,
    degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroup_l0_B0_noA5D0_Rest610,
    degreeZeroDeltaGroupPolynomial610,
    degreeZeroDeltaGroupNoA5Polynomial610, zero_mul, mul_zero, neg_zero,
    zero_smul, smul_zero, zero_add, add_zero, sub_zero, zero_pow_two,
    zero_pow_three, zero_pow_four, zero_pow_five]
  module

theorem highA_l0_B0_beta0_A5_combined_eq
    (delta : k) (A D0 : k[X]) :
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
        ((49 / 5184 * delta : k) • A ^ 5) =
      A ^ 5 * highA_l0_B0_beta0_A5Coefficient610 delta D0 := by
  simp only [highA_l0_B0_beta0_A5Coefficient610, smul_eq_C_mul]
  ring

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_l0_B0_D00_beta0
    (alpha delta epsilon zeta eta theta : k)
    (A C0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta eta
        theta A 0 C0 0 E0 =
      degreeZeroPrimitive_l0_B0_D00_beta0_610 delta zeta theta A C0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitive_l0_B0_D00_beta0_610,
    degreeZeroBaseGroupPolynomial610, degreeZeroAlphaGroupPolynomial610,
    degreeZeroBetaGroupPolynomial610, degreeZeroDeltaGroupPolynomial610,
    degreeZeroEpsilonGroupPolynomial610, degreeZeroZetaGroupPolynomial610,
    degreeZeroEtaGroupPolynomial610, degreeZeroThetaGroupPolynomial610,
    zero_mul, mul_zero, neg_zero, zero_smul, smul_zero, zero_add,
    add_zero, sub_zero, zero_pow_two, zero_pow_three, zero_pow_four,
    zero_pow_five]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_e0Terms_add
    (l alpha delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
        theta A B C0 D0 E0 =
      degreeZeroE0Terms610 l alpha theta A B C0 D0 E0 +
        degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 0 := by
  simp only [degreeZeroPrimitivePolynomial610, degreeZeroE0Terms610,
    degreeZeroBaseGroupPolynomial610, degreeZeroAlphaGroupPolynomial610,
    degreeZeroBetaGroupPolynomial610, degreeZeroDeltaGroupPolynomial610,
    degreeZeroEpsilonGroupPolynomial610, degreeZeroZetaGroupPolynomial610,
    degreeZeroEtaGroupPolynomial610, degreeZeroThetaGroupPolynomial610,
    zero_mul, mul_zero, neg_zero, zero_smul, smul_zero, zero_add,
    add_zero, sub_zero, zero_pow_two, zero_pow_three, zero_pow_four,
    zero_pow_five]
  module

theorem degreeZeroE0Terms610_eq_linear_mul
    (l alpha theta : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroE0Terms610 l alpha theta A B C0 D0 E0 =
      degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 * E0 := by
  simp only [degreeZeroE0Terms610, degreeZeroE0LinearPolynomial610,
    smul_eq_C_mul]
  ring

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_C03_faces_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
        (414720 / 2239488 : k) • (B * C0 ^ 3) +
          ((-(36288 / 559872 * beta : k)) • C0 ^ 3) +
            degreeZeroPrimitiveNoC03Rest610 l alpha beta delta epsilon zeta
              eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveNoC03Rest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupNoC03Polynomial610, degreeZeroBetaGroupPolynomial610,
    degreeZeroBetaGroupNoC03Polynomial610]
  module

theorem uniqueC0_cubicFaces_eq_coefficient_mul
    (l beta : k) (A B C0 : k[X]) :
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
        (414720 / 2239488 : k) • (B * C0 ^ 3) +
          ((-(36288 / 559872 * beta : k)) • C0 ^ 3) =
      uniqueC0_cubicCoefficient610 l beta A B * C0 ^ 3 := by
  simp only [uniqueC0_cubicCoefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

/-! ## Unique-`A` leftover chambers -/

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_eq_zero_of_le_zero {p : k[X]} (h : p.natDegree ≤ 0) :
    p.natDegree = 0 :=
  Nat.eq_zero_of_le_zero h

theorem natDegree_add_C_of_natDegree_eq_zero
    (c : k) {p : k[X]} (hp : p.natDegree = 0) :
    (p + C c).natDegree = 0 := by
  have hle : (p + C c).natDegree ≤ 0 :=
    (natDegree_add_le p (C c)).trans (max_le (hp.le) (by simp [natDegree_C]))
  exact natDegree_eq_zero_of_le_zero hle

theorem highA_l0_constB_A6Coefficient610_natDegree_eq_zero
    (beta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (highA_l0_constB_A6Coefficient610 beta B).natDegree = 0 := by
  have hsmul : ((-(62720 / 2239488 : k)) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hc : (C (2695 / 559872 * beta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((-(62720 / 2239488 : k)) • B +
      C (2695 / 559872 * beta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

theorem highA_l0_B0_beta0_A5Coefficient610_natDegree_eq_zero
    (delta : k) {D0 : k[X]} (hD : D0.natDegree = 0) :
    (highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree = 0 := by
  have hsmul : ((92160 / 2239488 : k) • D0).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ D0).trans hD.le
  have hc : (C (49 / 5184 * delta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_const_A6_ne
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hB : B.natDegree = 0)
    (hK : highA_l0_constB_A6Coefficient610 beta B ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hKdeg :
      (highA_l0_constB_A6Coefficient610 beta B).natDegree = 0 :=
    highA_l0_constB_A6Coefficient610_natDegree_eq_zero beta hB
  have hlead :
      (A ^ 6 * highA_l0_constB_A6Coefficient610 beta B).natDegree =
        6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 6 hA) hK, natDegree_pow, hKdeg, add_zero]
  have hrest :
      (degreeZeroPrimitiveHighA_l0_noA6_Rest610 alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0).natDegree <
        6 * A.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroBaseGroupHighA_noA6B_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_l0_noA6_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6_combined_add_rest,
    highA_l0_constB_A6_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_D0_pos
    (alpha delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hDpos : 0 < D0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (92160 / 2239488 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((92160 / 2239488 : k) • (A ^ 5 * D0)).natDegree =
        5 * A.natDegree + D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 5 hA) hDne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitive_l0_B0_beta0_noA5D0_Rest610 alpha delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        5 * A.natDegree + D0.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hDlt, hE⟩
    have hbase :
        (degreeZeroBaseGroup_l0_B0_noA5D0_Rest610 A C0 D0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroBaseGroup_l0_B0_noA5D0_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitive_l0_B0_beta0_noA5D0_Rest610]
    exact natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610 hbase (natDegree_smul_lt610 alpha halpha))
              (natDegree_smul_lt610 delta hdelta))
            (natDegree_smul_lt610 epsilon hepsilon))
          (natDegree_smul_lt610 zeta hzeta))
        (natDegree_smul_lt610 eta heta))
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A5D0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
    (alpha delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hD : D0.natDegree = 0)
    (hK : highA_l0_B0_beta0_A5Coefficient610 delta D0 ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha 0 delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hKdeg :
      (highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree = 0 :=
    highA_l0_B0_beta0_A5Coefficient610_natDegree_eq_zero delta hD
  have hlead :
      (A ^ 5 * highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree =
        5 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 5 hA) hK, natDegree_pow, hKdeg, add_zero]
  have hrest :
      (degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610 alpha delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        5 * A.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hDlt, hE⟩
    have hbase :
        (degreeZeroBaseGroup_l0_B0_noA5D0_Rest610 A C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroBaseGroup_l0_B0_noA5D0_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupNoA5Polynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroDeltaGroupNoA5Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitive_l0_B0_beta0_noA5_Rest610]
    exact natDegree_add_lt610
      (natDegree_add_lt610
        (natDegree_add_lt610
          (natDegree_add_lt610
            (natDegree_add_lt610
              (natDegree_add_lt610 hbase (natDegree_smul_lt610 alpha halpha))
              (natDegree_smul_lt610 delta hdelta))
            (natDegree_smul_lt610 epsilon hepsilon))
          (natDegree_smul_lt610 zeta hzeta))
        (natDegree_smul_lt610 eta heta))
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A5_combined_add_rest,
    highA_l0_B0_beta0_A5_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

/-- Primitive at `L = 0`, `B = 0`, `D₀ = 0`, `β = 0`, `δ = 0` with the
face `A⁴` deleted. -/
def degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610
    (zeta theta : k) (A C0 E0 : k[X]) : k[X] :=
  (40 / 192 * zeta : k) • (A ^ 2 * C0) -
    (48 / 192 * zeta : k) • C0 ^ 2 +
    (7 / 216 * theta : k) • A ^ 3 -
    (36 / 216 * theta : k) • (A * C0) +
    theta • E0

theorem degreeZeroPrimitive_l0_B0_D00_delta0_eq_A4_add_rest
    (zeta theta : k) (A C0 E0 : k[X]) :
    degreeZeroPrimitive_l0_B0_D00_beta0_610 0 zeta theta A C0 E0 =
      (-(7 / 192 * zeta : k)) • A ^ 4 +
        degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610 zeta theta A C0
          E0 := by
  simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610,
    degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero, zero_add]
  module

theorem degreeZeroPrimitive_l0_B0_D00_delta0_zeta0_eq_A3_add_rest
    (theta : k) (A C0 E0 : k[X]) :
    degreeZeroPrimitive_l0_B0_D00_beta0_610 0 0 theta A C0 E0 =
      (7 / 216 * theta : k) • A ^ 3 +
        ((-(36 / 216 * theta : k)) • (A * C0) + theta • E0) := by
  simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero, zero_add]
  module

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
    (alpha epsilon zeta eta theta j : k)
    (A C0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha 0 0 epsilon zeta eta
            theta A 0 C0 0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha 0 0 epsilon zeta eta
          theta A 0 C0 0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hApos : 0 < A.natDegree := hcone.1
  have hC : C0.natDegree < A.natDegree := hcone.2.2.1
  have hE : E0.natDegree < A.natDegree := hcone.2.2.2.2
  rw [degreeZeroPrimitivePolynomial610_eq_l0_B0_D00_beta0] at hdeg
  by_cases hzeta : zeta = 0
  · subst hzeta
    by_cases htheta : theta = 0
    · subst htheta
      have hle :
          (degreeZeroPrimitive_l0_B0_D00_beta0_610 0 0 0 A C0 E0).natDegree ≤
            0 := by
        simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610, zero_smul,
          zero_mul, smul_zero, add_zero, sub_zero, zero_add]
        simp [natDegree_zero]
      omega
    · have hc : (7 / 216 * theta : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) htheta
      have hA : A ≠ 0 := by
        intro hA0
        simp [hA0] at hApos
      have hlead :
          ((7 / 216 * theta : k) • A ^ 3).natDegree =
            3 * A.natDegree := by
        rw [natDegree_smul _ hc, natDegree_pow]
      have hrest :
          ((-(36 / 216 * theta : k)) • (A * C0) + theta • E0).natDegree <
            3 * A.natDegree := by
        have hAC :
            ((-(36 / 216 * theta : k)) • (A * C0)).natDegree <
              3 * A.natDegree := by
          compute_degree
          omega
        have hE0 : (theta • E0).natDegree < 3 * A.natDegree := by
          compute_degree
          omega
        exact natDegree_add_lt610 hAC hE0
      rw [degreeZeroPrimitive_l0_B0_D00_delta0_zeta0_eq_A3_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
        at hdeg
      omega
  · have hc : (-(7 / 192 * zeta : k)) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hzeta)
    have hA : A ≠ 0 := by
      intro hA0
      simp [hA0] at hApos
    have hlead :
        ((-(7 / 192 * zeta : k)) • A ^ 4).natDegree =
          4 * A.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest :
        (degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610 zeta theta A C0
            E0).natDegree <
          4 * A.natDegree := by
      simp only [degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610]
      compute_degree
      omega
    rw [degreeZeroPrimitive_l0_B0_D00_delta0_eq_A4_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
    omega

end HighAResidualCone610

/-! ## Unique nonconstant `C₀` (cubic face) -/

section UniqueC0Cone610

variable {k : Type*} [Field k] [CharZero k]

theorem uniqueC0_cubicCoefficient610_natDegree_eq_zero
    (l beta : k) {A B : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0) :
    (uniqueC0_cubicCoefficient610 l beta A B).natDegree = 0 := by
  have hA' : ((419904 / 2239488 * l : k) • A).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ A).trans hA.le
  have hB' : ((414720 / 2239488 : k) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hc : (C (-(36288 / 559872 * beta : k)) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((419904 / 2239488 * l : k) • A +
      (414720 / 2239488 : k) • B +
      C (-(36288 / 559872 * beta : k))).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans <| max_le
      ((natDegree_add_le _ _).trans (max_le hA' hB')) hc.le

set_option maxHeartbeats 16000000 in
theorem uniqueNonconstantC0_impossible_of_cubic_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hCpos : 0 < C0.natDegree) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hK : uniqueC0_cubicCoefficient610 l beta A B ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hKdeg :
      (uniqueC0_cubicCoefficient610 l beta A B).natDegree = 0 :=
    uniqueC0_cubicCoefficient610_natDegree_eq_zero l beta hA hB
  have hlead :
      (uniqueC0_cubicCoefficient610 l beta A B * C0 ^ 3).natDegree =
        3 * C0.natDegree := by
    rw [natDegree_mul hK (pow_ne_zero 3 hCne), natDegree_pow, hKdeg,
      zero_add]
  have hrest :
      (degreeZeroPrimitiveNoC03Rest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree <
        3 * C0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupNoC03Polynomial610 l A B C0 D0 E0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroBaseGroupNoC03Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoC03Polynomial610 A B C0 D0 E0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroBetaGroupNoC03Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          3 * C0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveNoC03Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_C03_faces_add_rest,
    uniqueC0_cubicFaces_eq_coefficient_mul,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end UniqueC0Cone610

/-! ## Unique nonconstant `E₀` with `β = 0` and `deg E₀ ≥ 2` -/

section UniqueE0BetaZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two
    (l alpha delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hEpos : 1 < E0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rw [degreeZeroPrimitivePolynomial610_eq_e0Terms_add,
    degreeZeroE0Terms610_eq_linear_mul] at hdeg
  have hlin :
      (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0).natDegree ≤
        0 := by
    simp only [degreeZeroE0LinearPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
    compute_degree
    omega
  have hfree :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 0).natDegree ≤
        0 := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroBaseGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 (0 : k[X])).natDegree ≤
          0 := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitivePolynomial610]
    exact natDegree_add8_le610 hbase
      (natDegree_smul_le_of_le610 alpha halpha)
      (natDegree_smul_le_of_le610 (0 : k) hbetaG)
      (natDegree_smul_le_of_le610 delta hdelta)
      (natDegree_smul_le_of_le610 epsilon hepsilon)
      (natDegree_smul_le_of_le610 zeta hzeta)
      (natDegree_smul_le_of_le610 eta heta)
      (natDegree_smul_le_of_le610 theta htheta)
  by_cases hL : degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 = 0
  · rw [hL, zero_mul, zero_add] at hdeg
    omega
  · have hEne : E0 ≠ 0 := by
      intro hE0
      simp [hE0] at hEpos
    have hLdeg :
        (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0).natDegree =
          0 :=
      natDegree_eq_zero_of_le_zero hlin
    have hlead :
        (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 * E0).natDegree =
          E0.natDegree := by
      rw [natDegree_mul hL hEne, hLdeg, zero_add]
    have hrest :
        (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
            theta A B C0 D0 0).natDegree <
          E0.natDegree :=
      hfree.trans_lt (Nat.zero_lt_of_lt hEpos)
    rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
    omega

end UniqueE0BetaZero610

/-! ## Unique-`B` with `A⁶ B` leading -/

section HighBA6BCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem uniqueHighB_impossible_of_A6B_leads
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : A6BLeadsHighBCone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hAB⟩
  have hAne : A ≠ 0 := by
    intro hA0
    simp [hA0, natDegree_zero] at hAB
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(62720 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(62720 / 2239488 : k)) • (A ^ 6 * B)).natDegree =
        6 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 6 hAne) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveNoA6B610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        6 * A.natDegree + B.natDegree := by
    have hA7 :
        ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree <
          6 * A.natDegree + B.natDegree := by
      compute_degree
      omega
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBaseGroupHighA_noA6B_Rest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htail :
        (degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      simp only [degreeZeroPrimitiveHighA_noA6B_Rest610]
      exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
        (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
        (natDegree_smul_lt610 epsilon hepsilon)
        (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
        (natDegree_smul_lt610 theta htheta)
    simp only [degreeZeroPrimitiveNoA6B610]
    exact natDegree_add_lt610 hA7 htail
  rw [degreeZeroPrimitivePolynomial610_eq_A6B_add_noA6B_withA7,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBA6BCone610

/-! ## Mixed constant-`(A,B,C₀)` high-`D₀` with `β = 0` -/

section MixedD0E0BetaZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem mixedConstABC_beta0_D0_leads_impossible
    (l alpha delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hDpos : 0 < D0.natDegree)
    (hE : E0.natDegree < 2 * D0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (-(829440 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(829440 / 2239488 : k)) • D0 ^ 3).natDegree =
        3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighDRest610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        3 * D0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroBaseGroupHighDRest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        ((0 : k) • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      rw [zero_smul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          3 * D0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighDRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      hbetaG
      (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_D3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end MixedD0E0BetaZero610

/-! ## Honest residual -/

section ResidualClosure610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Exact residual after the leftover unique-face cones of the scale-zero
cascade are closed.

The free core has polynomial representatives and the integrated primitive
has Newton degree one.  In addition to the parent cascade, the unique-`A`
chamber `L = 0` with `B` constant is empty unless the combined `A⁶`
coefficient vanishes, the unique-`A` chamber `L = 0`, `B = 0`, `β = 0`
is empty unless `D₀` is a nonzero constant whose combined `A⁵`
coefficient vanishes (and then `δ` is constrained), a unique nonconstant
`C₀` with nonzero cubic coefficient is empty, a unique nonconstant `E₀`
with `β = 0` and `deg E₀ ≥ 2` is empty, the unique-`B` chamber
`2 deg B < 3 deg A` is empty, and the mixed constant-`(A,B,C₀)` high-`D₀`
chamber with `β = 0` and `deg E₀ < 2 deg D₀` is empty.

Remaining named cones: the unique-`A` `A⁶`-cancelled chamber
`L = 0`, `deg B = 0`, `B ≠ 0`, `β = (64/11) B`; the unique-`A`
`A⁵`-cancelled chamber `L = 0`, `B = 0`, `β = 0`, `D₀` a nonzero
constant, `δ = -(640/147) D₀`; unique nonconstant `C₀` of degree one
with vanishing cubic (and, if present, quadratic) faces; unique
nonconstant `E₀` of degree one with `β = 0` and nonzero linear
coefficient; the unique-`B` tie `3 deg A = 2 deg B`; unique-high `C₀`
with at least one other letter nonconstant; unique-high `D₀` with `A`
nonconstant, or with `E₀` of degree at least `2 deg D₀`; unique-high
`E₀` with another letter nonconstant; and every cone in which two or
more letters share the maximal degree.  The already-constant first
integrals `κ, λ, μ` and the weight-seventy residual `ο` are not
consumed. -/
theorem normalized610ScaleZero_coneResidualClosureResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      (UniqueHighACone610 A B C0 D0 E0 →
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0) ∧
          (B ≠ 0 → highA_l0_constB_A6Coefficient610 beta B = 0) ∧
          (B = 0 →
            D0.natDegree = 0 ∧ D0 ≠ 0 ∧
              highA_l0_B0_beta0_A5Coefficient610 delta D0 = 0)) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧
          uniqueC0_cubicCoefficient610 l beta A B ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 1 < E0.natDegree ∧ beta = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree < 2 * D0.natDegree ∧
          beta = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hnonconst, hHighA, hExtB, hBonly, hDonly, hEonly⟩ :=
    normalized610ScaleZero_coneCascadeResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, hnonconst, ?_, hExtB, ?_, hBonly, hDonly, hEonly, ?_, ?_, ?_⟩
  · intro hcone
    have hparent := hHighA hcone
    refine ⟨hparent.1, hparent.2.1, hparent.2.2, ?_, ?_⟩
    · intro hBne
      by_contra hKne
      have hl0 : l = 0 := hparent.1
      have hBdeg : B.natDegree = 0 := hparent.2.1
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_const_A6_ne alpha beta delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hBdeg
        hKne hder
    · intro hB0
      have hl0 : l = 0 := hparent.1
      have hbeta0 : beta = 0 := hparent.2.2 hB0
      subst hl0
      subst hB0
      subst hbeta0
      have hD0 : D0.natDegree = 0 := by
        by_contra hDpos
        exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_D0_pos
          alpha delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv
          hcone (Nat.pos_of_ne_zero hDpos) hder
      refine ⟨hD0, ?_, ?_⟩
      · intro hDzero
        subst hDzero
        have hdelta0 : delta = 0 := by
          by_contra hdeltane
          have hK :
              highA_l0_B0_beta0_A5Coefficient610 delta (0 : k[X]) ≠ 0 := by
            simp only [highA_l0_B0_beta0_A5Coefficient610, smul_zero,
              zero_add]
            exact C_ne_zero.mpr
              (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num))
                hdeltane)
          exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
            alpha delta epsilon zeta eta theta (j / t) A C0 0 E0 hjdiv
            hcone (by simp [natDegree_zero]) hK hder
        subst hdelta0
        exact uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
          alpha epsilon zeta eta theta (j / t) A C0 E0 hjdiv hcone hder
      · by_contra hKne
        exact uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
          alpha delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv
          hcone hD0 hKne hder
  · intro hcone
    exact uniqueHighB_impossible_of_A6B_leads l alpha beta delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hder
  · intro hC
    exact uniqueNonconstantC0_impossible_of_cubic_ne l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hC.1 hC.2.1
      hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2.1 hC.2.2.2.2.2 hder
  · intro hE
    have hbeta0 : beta = 0 := hE.2.2.2.2.2
    subst hbeta0
    exact uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two l alpha
      delta epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hE.1 hE.2.1
      hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hder
  · intro hM
    have hbeta0 : beta = 0 := hM.2.2.2.2.2
    subst hbeta0
    exact mixedConstABC_beta0_D0_leads_impossible l alpha delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hM.1 hM.2.1 hM.2.2.1
      hM.2.2.2.1 hM.2.2.2.2.1 hder

end ResidualClosure610

#print axioms UniqueHighC0Cone610
#print axioms UniqueHighD0Cone610
#print axioms UniqueHighE0Cone610
#print axioms A6BLeadsHighBCone610
#print axioms highA_l0_constB_A6Coefficient610
#print axioms highA_l0_B0_beta0_A5Coefficient610
#print axioms uniqueC0_cubicCoefficient610
#print axioms uniqueHighA_impossible_of_l_zero_B_const_A6_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_D0_pos
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_zero_A5_ne
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_D0_zero_delta_zero
#print axioms uniqueNonconstantC0_impossible_of_cubic_ne
#print axioms uniqueNonconstantE0_impossible_of_beta_zero_deg_ge_two
#print axioms uniqueHighB_impossible_of_A6B_leads
#print axioms mixedConstABC_beta0_D0_leads_impossible
#print axioms normalized610ScaleZero_coneResidualClosureResidual

end Max11DegreeRoutes

