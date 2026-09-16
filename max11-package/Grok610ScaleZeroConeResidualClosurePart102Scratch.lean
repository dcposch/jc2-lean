import Grok610ScaleZeroConeResidualClosurePart101Scratch

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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

theorem degreeZeroE0Terms610_eq_linear_mul
    (l alpha theta : k) (A B C0 D0 E0 : k[X]) :
    degreeZeroE0Terms610 l alpha theta A B C0 D0 E0 =
      degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0 * E0 := by
  simp only [degreeZeroE0Terms610, degreeZeroE0LinearPolynomial610,
    smul_eq_C_mul]
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

theorem uniqueC0_cubicFaces_eq_coefficient_mul
    (l beta : k) (A B C0 : k[X]) :
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
        (414720 / 2239488 : k) • (B * C0 ^ 3) +
          ((-(36288 / 559872 * beta : k)) • C0 ^ 3) =
      uniqueC0_cubicCoefficient610 l beta A B * C0 ^ 3 := by
  simp only [uniqueC0_cubicCoefficient610, smul_eq_C_mul]
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

section HighAResidualCone610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_add_C_of_natDegree_eq_zero
    (c : k) {p : k[X]} (hp : p.natDegree = 0) :
    (p + C c).natDegree = 0 := by
  have hle : (p + C c).natDegree ≤ 0 :=
    (natDegree_add_le p (C c)).trans (max_le (hp.le) (by simp [natDegree_C]))
  exact natDegree_eq_zero_of_le_zero610 hle

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

theorem highA_l0_constB_A6Coefficient610_natDegree_eq_zero
    (beta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (highA_l0_constB_A6Coefficient610 beta B).natDegree = 0 := by
  have hsmul : ((-(62720 / 2239488 : k)) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hc : (C (2695 / 559872 * beta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((-(62720 / 2239488 : k)) • B +
      C (2695 / 559872 * beta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

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

theorem highA_l0_B0_beta0_A5Coefficient610_natDegree_eq_zero
    (delta : k) {D0 : k[X]} (hD : D0.natDegree = 0) :
    (highA_l0_B0_beta0_A5Coefficient610 delta D0).natDegree = 0 := by
  have hsmul : ((92160 / 2239488 : k) • D0).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ D0).trans hD.le
  have hc : (C (49 / 5184 * delta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((92160 / 2239488 : k) • D0 + C (49 / 5184 * delta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans (max_le hsmul hc.le)

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

theorem degreeZeroPrimitive_l0_B0_D00_delta0_zeta0_eq_A3_add_rest
    (theta : k) (A C0 E0 : k[X]) :
    degreeZeroPrimitive_l0_B0_D00_beta0_610 0 0 theta A C0 E0 =
      (7 / 216 * theta : k) • A ^ 3 +
        ((-(36 / 216 * theta : k)) • (A * C0) + theta • E0) := by
  simp only [degreeZeroPrimitive_l0_B0_D00_beta0_610, zero_mul, zero_smul,
    smul_zero, add_zero, sub_zero, zero_add]
  module

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
  exact natDegree_eq_zero_of_le_zero610 <|
    (natDegree_add_le _ _).trans <| max_le
      ((natDegree_add_le _ _).trans (max_le hA' hB')) hc.le

end UniqueC0Cone610

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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
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

end HighAResidualCone610

end Max11DegreeRoutes
