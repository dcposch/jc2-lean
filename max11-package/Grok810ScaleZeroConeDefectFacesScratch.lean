import Grok810ScaleZeroConeDefectFacesSpeedTPart102Scratch

/-! # Scale-zero first-integral faces for the normalized `(8,10)`, `H = 0` leaf

Continuation of `Grok810ScaleZeroConeEliminationScratch` on the constant
core `H = (C t)²`.  That file closed the unique Newton faces of the
degree-one primitive and recorded the leftover cones in
`normalized810ScaleZero_coneEliminationResidual`.  The unused first
integrals of the same monic depression — in particular the weight-`98`
cleared defect `ξ` and the weight-`105` cleared defect `ο`, together
with the weight-`84` integral `μ` — are ground constants on both
constant faces of `N`.

CAS job `derive_810_scale_zero_cone_defect_faces.py` (outer degrees
`(8,10)`, leading `h⁴`, `h⁵` with `h` a nonzero constant) substitutes
the triangular Faber constants into `xiResidual810`,
`omicronResidual810`, and `muResidual810`.  After that substitution
the load-free faces

* `-(165/65536) A⁷` of `ξ`, of degree `7 deg A`,
* `-(21/4096) B⁵` of `ο`, of degree `5 deg B`,
* `-(5/128) C₀³` of `μ`, of degree `3 deg C₀`,
* `-(5/128) D₀³` of `ο`, of degree `3 deg D₀`,
* `(5/32) E₀²` of `μ`, of degree `2 deg E₀`,
* `(5/32) F₀²` of `ξ`, of degree `2 deg F₀`

never meet a load term of equal degree (loads are ground constants).
Consequently a unique maximum among those weighted degrees is empty.
A constant free core is already empty by the parent.  Unique-`G₀` of
degree one with vanishing `G₀`-linear coefficients of `ξ`, `μ`, and
`ο` is recorded rather than forced (the primitive linear coefficient
`θ` is independent of those three).  Pair-ratio ties in which no
load-free face strictly leads are likewise recorded.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  The theorems
`normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

#print axioms AMaximalCone810
#print axioms UniqueHighBCone810
#print axioms BLeadsOmicronCone810
#print axioms UniqueHighC0Cone810
#print axioms C0LeadsMuCone810
#print axioms UniqueHighD0Cone810
#print axioms D0LeadsOmicronCone810
#print axioms E0LeadsMuCone810
#print axioms F0LeadsXiCone810
#print axioms UniqueHighG0DegOneCone810
#print axioms degreeZeroXiPolynomial810
#print axioms degreeZeroMuPolynomial810
#print axioms degreeZeroOmicronPolynomial810
#print axioms xiResidual810_eq_integrated
#print axioms muResidual810_eq_integrated
#print axioms omicronResidual810_eq_integrated
#print axioms algebraMap_degreeZeroXiPolynomial810
#print axioms algebraMap_degreeZeroMuPolynomial810
#print axioms algebraMap_degreeZeroOmicronPolynomial810
#print axioms xi_A7_impossible_of_A_maximal
#print axioms omicron_B5_impossible_of_B_leads
#print axioms mu_C03_impossible_of_C0_leads
#print axioms omicron_D03_impossible_of_D0_leads
#print axioms mu_E02_impossible_of_E0_leads
#print axioms xi_F02_impossible_of_F0_leads
#print axioms normalized810ScaleZero_defectPolynomials_eq_C
#print axioms normalized810ScaleZero_defectFaces_closed
#print axioms normalized810ScaleZero_coneDefectFacesResidual
#print axioms normalized810ScaleZero_impossible_of_defectFacesResidual

end Max11DegreeRoutes
