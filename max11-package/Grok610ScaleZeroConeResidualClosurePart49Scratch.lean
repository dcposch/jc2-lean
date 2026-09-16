import Grok610ScaleZeroConeResidualClosurePart102Scratch
import Grok610ScaleZeroConeResidualClosurePart101Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section UniqueE0BetaZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroE0LinearPolynomial610`. -/
private theorem astra4b_structural_degreeZeroE0LinearPolynomial610
    {l alpha theta : k} {A B C0 D0 : k[X]} :
    (degreeZeroE0LinearPolynomial610 l alpha theta A B C0 D0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max (max (4 * A.natDegree) ((3 * A.natDegree) + (B.natDegree))) ((2 * A.natDegree) + (C0.natDegree))) ((2 * A.natDegree) + (D0.natDegree))) ((A.natDegree) + (2 * B.natDegree))) (((A.natDegree) + (B.natDegree)) + (C0.natDegree))) (3 * B.natDegree)) ((B.natDegree) + (D0.natDegree))) (2 * C0.natDegree)) ((C0.natDegree) + (D0.natDegree))) ((2 * A.natDegree) + (B.natDegree))) ((A.natDegree) + (D0.natDegree))) ((B.natDegree) + (C0.natDegree))) (0) := by
  unfold degreeZeroE0LinearPolynomial610
  exact (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _)))))) (by simp only [natDegree_C, le_refl])))

set_option maxHeartbeats 64000000 in
/-- Structural degree certificate for `degreeZeroBaseGroupPolynomial610`. -/
private theorem astra4b_structural_degreeZeroBaseGroupPolynomial610
    {l : k} {A B C0 D0 E0 : k[X]} :
    (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree ≤
      max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (max (7 * A.natDegree) ((6 * A.natDegree) + (B.natDegree))) ((5 * A.natDegree) + (C0.natDegree))) ((5 * A.natDegree) + (D0.natDegree))) ((4 * A.natDegree) + (2 * B.natDegree))) (((4 * A.natDegree) + (B.natDegree)) + (C0.natDegree))) ((4 * A.natDegree) + (E0.natDegree))) ((3 * A.natDegree) + (3 * B.natDegree))) (((3 * A.natDegree) + (B.natDegree)) + (D0.natDegree))) (((3 * A.natDegree) + (B.natDegree)) + (E0.natDegree))) ((3 * A.natDegree) + (2 * C0.natDegree))) (((3 * A.natDegree) + (C0.natDegree)) + (D0.natDegree))) (((2 * A.natDegree) + (2 * B.natDegree)) + (C0.natDegree))) (((2 * A.natDegree) + (2 * B.natDegree)) + (D0.natDegree))) (((2 * A.natDegree) + (B.natDegree)) + (2 * C0.natDegree))) (((2 * A.natDegree) + (C0.natDegree)) + (E0.natDegree))) ((2 * A.natDegree) + (2 * D0.natDegree))) (((2 * A.natDegree) + (D0.natDegree)) + (E0.natDegree))) ((A.natDegree) + (4 * B.natDegree))) (((A.natDegree) + (3 * B.natDegree)) + (C0.natDegree))) (((A.natDegree) + (2 * B.natDegree)) + (E0.natDegree))) ((((A.natDegree) + (B.natDegree)) + (C0.natDegree)) + (D0.natDegree))) ((((A.natDegree) + (B.natDegree)) + (C0.natDegree)) + (E0.natDegree))) (((A.natDegree) + (B.natDegree)) + (2 * D0.natDegree))) ((A.natDegree) + (3 * C0.natDegree))) (((A.natDegree) + (2 * C0.natDegree)) + (D0.natDegree))) (5 * B.natDegree)) ((3 * B.natDegree) + (D0.natDegree))) ((3 * B.natDegree) + (E0.natDegree))) ((2 * B.natDegree) + (2 * C0.natDegree))) (((2 * B.natDegree) + (C0.natDegree)) + (D0.natDegree))) ((B.natDegree) + (3 * C0.natDegree))) (((B.natDegree) + (D0.natDegree)) + (E0.natDegree))) ((2 * C0.natDegree) + (E0.natDegree))) ((C0.natDegree) + (2 * D0.natDegree))) (((C0.natDegree) + (D0.natDegree)) + (E0.natDegree))) (3 * D0.natDegree) := by
  unfold degreeZeroBaseGroupPolynomial610
  exact (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_add_le _ _) (max_le_max (le_trans (natDegree_sub_le _ _) (max_le_max (le_trans (natDegree_smul_le _ _) natDegree_pow_le) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le)) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add natDegree_pow_le (le_refl _)))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) natDegree_pow_le))))) (le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le (Nat.add_le_add (le_trans natDegree_mul_le (Nat.add_le_add (le_refl _) (le_refl _))) (le_refl _)))))) (le_trans (natDegree_smul_le _ _) natDegree_pow_le)))

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
    apply le_trans astra4b_structural_degreeZeroE0LinearPolynomial610
    clear * - hA hB hC hD
    simp only [max_le_iff, natDegree_zero]
    repeat' apply And.intro
    all_goals omega
  have hfree :
      (degreeZeroPrimitivePolynomial610 l alpha 0 delta epsilon zeta eta
          theta A B C0 D0 0).natDegree ≤
        0 := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      apply le_trans astra4b_structural_degreeZeroBaseGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      apply le_trans astra4b_structural_degreeZeroAlphaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hbetaG :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 (0 : k[X])).natDegree ≤
          0 := by
      apply le_trans astra4b_structural_degreeZeroBetaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      apply le_trans astra4b_structural_degreeZeroDeltaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      apply le_trans astra4b_structural_degreeZeroEpsilonGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      apply le_trans astra4b_structural_degreeZeroZetaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      apply le_trans astra4b_structural_degreeZeroEtaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 (0 : k[X])).natDegree ≤
          0 := by
      apply le_trans astra4b_structural_degreeZeroThetaGroupPolynomial610
      clear * - hA hB hC hD
      simp only [max_le_iff, natDegree_zero]
      repeat' apply And.intro
      all_goals omega
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
      natDegree_eq_zero_of_le_zero610 hlin
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

end Max11DegreeRoutes
