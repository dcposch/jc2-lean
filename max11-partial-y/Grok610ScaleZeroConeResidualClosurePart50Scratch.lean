import Grok610ScaleZeroConeResidualClosurePart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section HighBA6BCone610

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
/-- Structural degree certificate for `degreeZeroBetaGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroBetaGroupPolynomial610
    {A B C0 D0 E0 : k[X]} :
    (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max (max (6 * A.natDegree) ((4 * A.natDegree) + (C0.natDegree))) ((3 * A.natDegree) + (2 * B.natDegree))) ((3 * A.natDegree) + (E0.natDegree))) (((2 * A.natDegree) + (B.natDegree)) + (D0.natDegree))) ((2 * A.natDegree) + (2 * C0.natDegree))) (((A.natDegree) + (2 * B.natDegree)) + (C0.natDegree))) (((A.natDegree) + (C0.natDegree)) + (E0.natDegree))) ((A.natDegree) + (2 * D0.natDegree))) (4 * B.natDegree)) ((2 * B.natDegree) + (E0.natDegree))) (((B.natDegree) + (C0.natDegree)) + (D0.natDegree))) (3 * C0.natDegree)) (2 * E0.natDegree) := by
  unfold degreeZeroBetaGroupPolynomial610
  exact (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

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
      apply lt_of_le_of_lt (le_trans (natDegree_smul_le _ _) natDegree_pow_le)
      clear * - hBpos hA hC hD hE hAB
      omega
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 l A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroBaseGroupHighA_noA6B_Rest610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroAlphaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroBetaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroDeltaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroEpsilonGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroZetaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroEtaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      apply lt_of_le_of_lt astra4b_structural_degreeZeroThetaGroupPolynomial610
      clear * - hBpos hA hC hD hE hAB
      simp only [max_lt_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
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

end Max11DegreeRoutes
