import LowScale68SecondaryFirstGapBoundaryFacePart15Scratch

/-! # Residual faces on the first-gap boundary `2g = n`

The tracked classifier
`maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68`
already gives `l = 0`, `ee.coeff(6n-g) = 0` and `a*b = 3*D_top` on
`2g = n`.  This module turns those two coefficient cancellations into
strict residual degree drops, selects the residual gap `h > g`, and
extracts the ordinary residual middle invariants throughout `g < h < 2g`.

After `l = 0` the heaviest quartic load is `beta A^3` at `6n`, while the
heaviest residual row-one load is `alpha A^3` against `C0'` at `10n-1`.
Both sit strictly below every displayed residual index on this wall, so
the next exact face is the ordinary middle pair rather than a new mixed
scalar system.  Closing the wall still needs the residual double / row-two
selector and the balanced row-one cubic scalar, supplied by
`LowScale68SecondaryFirstGapBoundary`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstGapBoundaryEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Residual degree drops after the classified wall -/

/-! ## Canonical support, drops, and residual gap -/

/-! ## Load cutoffs after `l = 0` on the wall -/

/-! ## Homogeneous residual middle coefficients on the wall -/

/-! ## Homogeneous residual double invariants on the wall -/

/-! ## Canonical residual middle face on the wall -/

end FirstGapBoundaryEndgame68

#print axioms secondaryDDefectPolynomial68_degree_lt_of_firstLoadWall
#print axioms firstSecondaryResidualDegreeDrops68_of_firstLoadWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallBoundary68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDrops68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualGap68
#print axioms cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_firstLoadWall
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstLoadWall
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstLoadWall
#print axioms polynomialSecondaryResidualBetweenFace68_of_firstLoadWall
#print axioms polynomialSecondaryResidualDoubleInvariants68_of_firstLoadWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualMiddleFace68

end Max11DegreeRoutes
