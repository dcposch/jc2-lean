import LowScale68SecondaryLaterDeepLowerEndgamePart23Scratch

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

end LaterDeepLowerEndgame68

#print axioms laterDeepLower_gap_lt_three_radius
#print axioms cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
#print axioms cubicLoadRowOnePolynomial68_degree_lt_firstFace_of_laterDeepLower
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_firstFace_of_laterDeepLower_open
#print axioms polynomialSecondaryClassified68_of_laterDeepLower_open
#print axioms secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68

end Max11DegreeRoutes
