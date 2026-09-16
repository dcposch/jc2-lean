import Grok610ScaleZeroConeCascadeScratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `C₀` cone. -/
def UniqueHighC0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    A.natDegree < C0.natDegree ∧
    B.natDegree < C0.natDegree ∧
    D0.natDegree < C0.natDegree ∧
    E0.natDegree < C0.natDegree

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `D₀` cone. -/
def UniqueHighD0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < D0.natDegree ∧
    A.natDegree < D0.natDegree ∧
    B.natDegree < D0.natDegree ∧
    C0.natDegree < D0.natDegree ∧
    E0.natDegree < D0.natDegree

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-max `E₀` cone. -/
def UniqueHighE0Cone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    A.natDegree < E0.natDegree ∧
    B.natDegree < E0.natDegree ∧
    C0.natDegree < E0.natDegree ∧
    D0.natDegree < E0.natDegree

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique-`B` subcone on which `A⁶ B` strictly outranks `B⁵`. -/
def A6BLeadsHighBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    2 * B.natDegree < 3 * A.natDegree

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Combined `A⁶` coefficient on the unique-`A` chamber `L = 0`,
`deg B = 0`. -/
def highA_l0_constB_A6Coefficient610 (beta : k) (B : k[X]) : k[X] :=
  (-(62720 / 2239488 : k)) • B + C (2695 / 559872 * beta : k)

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Combined `A⁵` coefficient on the unique-`A` chamber `L = 0`,
`B = 0`, `β = 0`, `D₀` constant. -/
def highA_l0_B0_beta0_A5Coefficient610 (delta : k) (D0 : k[X]) : k[X] :=
  (92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ExtraCones610

variable {k : Type*} [Field k] [CharZero k]

/-- Combined `C₀³` coefficient on a unique-nonconstant `C₀` chamber. -/
def uniqueC0_cubicCoefficient610 (l beta : k) (A B : k[X]) : k[X] :=
  (419904 / 2239488 * l : k) • A +
    (414720 / 2239488 : k) • B +
    C (-(36288 / 559872 * beta : k))

end ExtraCones610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive with the face `A⁶ B` deleted, `A⁷` retained. -/
def degreeZeroPrimitiveNoA6B610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 +
    degreeZeroPrimitiveHighA_noA6B_Rest610 l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- Base group at `L = 0`, `B = 0` with `A⁵ D₀` deleted. -/
def degreeZeroBaseGroup_l0_B0_noA5D0_Rest610
    (A C0 D0 E0 : k[X]) : k[X] :=
  (-(668160 / 2239488 : k)) • (A ^ 3 * C0 * D0) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

/-- Delta group with the face `A⁵` deleted. -/
def degreeZeroDeltaGroupNoA5Polynomial610 (A B C0 D0 : k[X]) : k[X] :=
  (-(360 / 5184 : k)) • (A ^ 3 * C0) -
    (600 / 5184 : k) • (A ^ 2 * B ^ 2) +
    (1440 / 5184 : k) • (A * B * D0) +
    (720 / 5184 : k) • (A * C0 ^ 2) +
    (720 / 5184 : k) • (B ^ 2 * C0) -
    (2160 / 5184 : k) • D0 ^ 2

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_eq_zero_of_le_zero610 {p : k[X]} (h : p.natDegree ≤ 0) :
    p.natDegree = 0 :=
  Nat.eq_zero_of_le_zero h

end HighAResidualCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive at `L = 0`, `B = 0`, `D₀ = 0`, `β = 0`, `δ = 0` with the
face `A⁴` deleted. -/
def degreeZeroPrimitive_l0_B0_D00_delta0_noA4_Rest610
    (zeta theta : k) (A C0 E0 : k[X]) : k[X] :=
  (40 / 192 * zeta : k) • (A ^ 2 * C0) -
    (48 / 192 * zeta : k) • C0 ^ 2 +
    (7 / 216 * theta : k) • A ^ 3 -
    (36 / 216 * theta : k) • (A * C0) +
    theta • E0

end HighAResidualCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

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

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

theorem highA_l0_constB_A6_combined_eq
    (beta : k) (A B : k[X]) :
    (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
        ((2695 / 559872 * beta : k) • A ^ 6) =
      A ^ 6 * highA_l0_constB_A6Coefficient610 beta B := by
  simp only [highA_l0_constB_A6Coefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ResidualSplittings610

variable {k : Type*} [Field k] [CharZero k]

theorem highA_l0_B0_beta0_A5_combined_eq
    (delta : k) (A D0 : k[X]) :
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
        ((49 / 5184 * delta : k) • A ^ 5) =
      A ^ 5 * highA_l0_B0_beta0_A5Coefficient610 delta D0 := by
  simp only [highA_l0_B0_beta0_A5Coefficient610, smul_eq_C_mul]
  ring

end ResidualSplittings610

end Max11DegreeRoutes
