import LowScale68SecondaryLargeGapLoadZeroFacePart16Scratch

/-! # Residual faces in the large-gap load-zero chamber

The tracked theorems
`maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68`
and
`maximalExpandedIntegratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL`
already give `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`n < 2g` and `g < n`.  Every first-face bound `2g < 3n` is free from
`g < n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle and double I4/I3 faces.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, the
heaviest cubic load is `beta A^2 B` at `7n-g`, and the heaviest row-two
product is `Ul C0'` at `9n-g-1`.  All three sit strictly below every
displayed residual index throughout `g < n`.  Row one at `12n-3g-1`
  remains load-free only on the extra window `3g < 2n`.  Closing the
chamber still needs residual one-forms and their row-one load split; this
module supplies their canonical classification and invariant-face inputs.

The existing `of_twoGap` / first-load-wall lemmas cannot be cited: their
`2g < n` or `2g = n` hypotheses are false even though the arithmetic
with `l = 0` and `g < n` remains strict.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## Residual degree drops after the classified face -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on `g < n` -/

/-! ## Homogeneous residual middle coefficients -/

/-! ## Homogeneous residual double invariants -/

/-! ## Canonical residual faces -/

end LargeGapLoadZeroEndgame68

#print axioms largeGapLoadZero_two_mul_gap_lt_three_radius
#print axioms secondaryDDefectPolynomial68_degree_lt_of_largeGapLoadZero
#print axioms firstSecondaryResidualDegreeDrops68_of_largeGapLoadZero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroBoundary68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDrops68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualGap68
#print axioms cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_largeGap
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
#print axioms polynomialSecondaryResidualBetweenFace68_of_largeGapLoadZero
#print axioms polynomialSecondaryResidualDoubleInvariants68_of_largeGapLoadZero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualMiddleFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualDoubleInvariants68

end Max11DegreeRoutes
