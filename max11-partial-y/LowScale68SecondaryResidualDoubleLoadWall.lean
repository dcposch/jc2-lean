import LowScale68SecondaryResidualDoubleLoadWallPart11Scratch

/-! # Mixed residual double face on the `(6,8)` wall `n = 3g`, `h = 2g`

On `n = 3g` the residual double face `9n-3g` collides with the Jacobian
load `l A^4` at degree `8n`.  Row two and row zero likewise meet the cores
`l A^5` and `l A^6` at `10n-1` and `12n-1`.  I3 and row one remain
load-free.  The five leading scalars force `l = b = c = 0`; residual
support `b ≠ 0 ∨ c ≠ 0` therefore excludes the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Abstract mixed numerators -/

/-! ## Scalar identities -/

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

/-! ## Term-by-term remainder degree bounds on `3g = n`

Cores, rest polynomials, Jacobian splits, and
`cubicLoadRowTwo/ZeroPolynomial68_eq_lCore_add_rest` are the tracked
definitions in `LowScale68SecondaryFirstLoadWallRemainder`.  Only the
wall-specific degree comparisons `3g = n` are restated here. -/

/-! ## Homogeneous residual one-forms at the wall indices -/

#print axioms residualDoubleLoadWallFace68_classify
#print axioms residualDoubleLoadWallFace68_impossible
#print axioms residualDoubleLoadWallFace68_classify_of_three_mul_gap_eq_radius
#print axioms residualDoubleLoadWallFourScalar68_eq_hom_add_load
#print axioms residualDoubleLoadWallTwoScalar68_eq_hom_add_load
#print axioms residualDoubleLoadWallZeroScalar68_eq_hom_add_load
#print axioms secondaryLoadInvariantFourPolynomial68_eq_core_add_rest
#print axioms cubicLoadRowTwoPolynomial68_eq_lCore_add_rest
#print axioms cubicLoadRowZeroPolynomial68_eq_lCore_add_rest
#print axioms cubicFirstIntegralFourPolynomial68_coeff_residualDoubleLoadWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_residualDoubleLoadWall
#print axioms cubicLoadRowTwoPolynomial68_coeff_residualDoubleLoadWall
#print axioms cubicLoadRowZeroPolynomial68_coeff_residualDoubleLoadWall
#print axioms secondaryResidualRowTwoPolynomial68_coeff_doubleLoadWall
#print axioms secondaryResidualRowOnePolynomial68_coeff_doubleLoadWall
#print axioms secondaryResidualRowZeroPolynomial68_coeff_doubleLoadWall

end Max11DegreeRoutes
