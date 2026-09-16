import Grok610ScaleZeroConeResidualClosurePart101Scratch
import Grok610ScaleZeroConeResidualClosurePart102Scratch

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

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroBaseGroupHighA_noA6B_Rest610`. -/
private theorem astra4b_structural_degreeZeroBaseGroupHighA_noA6B_Rest610
    {l : k} {A B C0 D0 E0 : k[X]} :
    (degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max ((5 * A.natDegree) + (C0.natDegree)) ((5 * A.natDegree) + (D0.natDegree))) ((4 * A.natDegree) + (2 * B.natDegree))) (((4 * A.natDegree) + (B.natDegree)) + (C0.natDegree))) ((4 * A.natDegree) + (E0.natDegree))) ((3 * A.natDegree) + (3 * B.natDegree))) (((3 * A.natDegree) + (B.natDegree)) + (D0.natDegree))) (((3 * A.natDegree) + (B.natDegree)) + (E0.natDegree))) ((3 * A.natDegree) + (2 * C0.natDegree))) (((3 * A.natDegree) + (C0.natDegree)) + (D0.natDegree))) (((2 * A.natDegree) + (2 * B.natDegree)) + (C0.natDegree))) (((2 * A.natDegree) + (2 * B.natDegree)) + (D0.natDegree))) (((2 * A.natDegree) + (B.natDegree)) + (2 * C0.natDegree))) (((2 * A.natDegree) + (C0.natDegree)) + (E0.natDegree))) ((2 * A.natDegree) + (2 * D0.natDegree))) (((2 * A.natDegree) + (D0.natDegree)) + (E0.natDegree))) ((A.natDegree) + (4 * B.natDegree))) (((A.natDegree) + (3 * B.natDegree)) + (C0.natDegree))) (((A.natDegree) + (2 * B.natDegree)) + (E0.natDegree))) ((((A.natDegree) + (B.natDegree)) + (C0.natDegree)) + (D0.natDegree))) ((((A.natDegree) + (B.natDegree)) + (C0.natDegree)) + (E0.natDegree))) (((A.natDegree) + (B.natDegree)) + (2 * D0.natDegree))) ((A.natDegree) + (3 * C0.natDegree))) (((A.natDegree) + (2 * C0.natDegree)) + (D0.natDegree))) (5 * B.natDegree)) ((3 * B.natDegree) + (D0.natDegree))) ((3 * B.natDegree) + (E0.natDegree))) ((2 * B.natDegree) + (2 * C0.natDegree))) (((2 * B.natDegree) + (C0.natDegree)) + (D0.natDegree))) ((B.natDegree) + (3 * C0.natDegree))) (((B.natDegree) + (D0.natDegree)) + (E0.natDegree))) ((2 * C0.natDegree) + (E0.natDegree))) ((C0.natDegree) + (2 * D0.natDegree))) (((C0.natDegree) + (D0.natDegree)) + (E0.natDegree))) (3 * D0.natDegree) := by
  unfold degreeZeroBaseGroupHighA_noA6B_Rest610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroAlphaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroAlphaGroupPolynomial610
    {A B C0 D0 E0 : k[X]} :
    (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max ((5 * A.natDegree) + (B.natDegree)) ((4 * A.natDegree) + (D0.natDegree))) (((3 * A.natDegree) + (B.natDegree)) + (C0.natDegree))) ((2 * A.natDegree) + (3 * B.natDegree))) (((2 * A.natDegree) + (B.natDegree)) + (E0.natDegree))) (((2 * A.natDegree) + (C0.natDegree)) + (D0.natDegree))) (((A.natDegree) + (2 * B.natDegree)) + (D0.natDegree))) (((A.natDegree) + (B.natDegree)) + (2 * C0.natDegree))) (((A.natDegree) + (D0.natDegree)) + (E0.natDegree))) ((3 * B.natDegree) + (C0.natDegree))) (((B.natDegree) + (C0.natDegree)) + (E0.natDegree))) ((B.natDegree) + (2 * D0.natDegree))) ((2 * C0.natDegree) + (D0.natDegree)) := by
  unfold degreeZeroAlphaGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))))))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroBetaGroupNoA6Polynomial610`. -/
private theorem astra4b_structural_degreeZeroBetaGroupNoA6Polynomial610
    {A B C0 D0 E0 : k[X]} :
    (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max ((4 * A.natDegree) + (C0.natDegree)) ((3 * A.natDegree) + (2 * B.natDegree))) ((3 * A.natDegree) + (E0.natDegree))) (((2 * A.natDegree) + (B.natDegree)) + (D0.natDegree))) ((2 * A.natDegree) + (2 * C0.natDegree))) (((A.natDegree) + (2 * B.natDegree)) + (C0.natDegree))) (((A.natDegree) + (C0.natDegree)) + (E0.natDegree))) ((A.natDegree) + (2 * D0.natDegree))) (4 * B.natDegree)) ((2 * B.natDegree) + (E0.natDegree))) (((B.natDegree) + (C0.natDegree)) + (D0.natDegree))) (3 * C0.natDegree)) (2 * E0.natDegree) := by
  unfold degreeZeroBetaGroupNoA6Polynomial610
  exact (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroDeltaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroDeltaGroupPolynomial610
    {A B C0 D0 : k[X]} :
    (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤
      max (max (max (max (max (max (5 * A.natDegree) ((3 * A.natDegree) + (C0.natDegree))) ((2 * A.natDegree) + (2 * B.natDegree))) (((A.natDegree) + (B.natDegree)) + (D0.natDegree))) ((A.natDegree) + (2 * C0.natDegree))) ((2 * B.natDegree) + (C0.natDegree))) (2 * D0.natDegree) := by
  unfold degreeZeroDeltaGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroEpsilonGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroEpsilonGroupPolynomial610
    {A B C0 D0 : k[X]} :
    (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤
      max (max (max (max ((3 * A.natDegree) + (B.natDegree)) ((2 * A.natDegree) + (D0.natDegree))) (((A.natDegree) + (B.natDegree)) + (C0.natDegree))) (3 * B.natDegree)) ((C0.natDegree) + (D0.natDegree)) := by
  unfold degreeZeroEpsilonGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))))))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroZetaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroZetaGroupPolynomial610
    {A B C0 D0 : k[X]} :
    (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤
      max (max (max (max (4 * A.natDegree) ((2 * A.natDegree) + (C0.natDegree))) ((A.natDegree) + (2 * B.natDegree))) ((B.natDegree) + (D0.natDegree))) (2 * C0.natDegree) := by
  unfold degreeZeroZetaGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroEtaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroEtaGroupPolynomial610
    {A B C0 D0 : k[X]} :
    (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤
      max (max ((2 * A.natDegree) + (B.natDegree)) ((A.natDegree) + (D0.natDegree))) ((B.natDegree) + (C0.natDegree)) := by
  unfold degreeZeroEtaGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))))))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroThetaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroThetaGroupPolynomial610
    {A B C0 E0 : k[X]} :
    (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree ≤
      max (max (max (3 * A.natDegree) ((A.natDegree) + (C0.natDegree))) (2 * B.natDegree)) (E0.natDegree) := by
  unfold degreeZeroThetaGroupPolynomial610
  exact (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_refl _))))

open private zero_pow_two from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_three from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_four from Grok610ScaleZeroConeResidualClosurePart101Scratch in
open private zero_pow_five from Grok610ScaleZeroConeResidualClosurePart101Scratch in
set_option maxHeartbeats 64000000 in
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
      apply lt_of_le_of_lt astra4b_structural_degreeZeroBaseGroupHighA_noA6B_Rest610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroAlphaGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroBetaGroupNoA6Polynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroDeltaGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroEpsilonGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroZetaGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroEtaGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroThetaGroupPolynomial610
      clear * - hApos hBlt hB hC hD hE
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
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

end HighAResidualCone610

end Max11DegreeRoutes
