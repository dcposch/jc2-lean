import LowScale68SecondaryRelaxedFirstFacePart23Scratch

/-! # Relaxed first `(6,8)` secondary face after `l = 0`

The tracked extraction in `LowScale68SecondaryExtraction` and
`LowScale68SecondaryOneForms` uses the chamber `2g < n` because the Jacobian
load `l A^4` and the `l`-pieces of the integrated coefficients sit on or
above the first secondary face once `2g ≥ n`.  In the complementary
large-gap chamber the quartic invariant forces `l = 0`.  With that
hypothesis the same leading coefficients can be re-extracted under the
weaker old-weight cutoff `2g < 3n`, except the second one-form row, whose
`alpha A^2` load meets the face as soon as `g ≥ n`.

Exact chambers, remaining loads otherwise arbitrary:

* invariants `F₄`, `F₃` and one-forms `F₂`, `F₀`: `2g < 3n`
* one-form `F₁`: `g < n` (or `2g < 3n` after the extra vanishing `alpha = 0`)
* full five-face classification `e = 0 ∧ a*b = 3*d`: needs `F₁`
* four-equation classification without `F₁`, under `2g < 3n`:
  `(e = 0 ∧ a*b = 3*d) ∨ (e = 0 ∧ c = 0 ∧ a*b = d) ∨ (b = c = d = 0)`
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedSecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Abstract classification under the relaxed radius gap -/

/-! ## Load degree cutoffs after `l = 0` -/

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

/-! ## One-form load cutoffs after `l = 0` -/

end RelaxedSecondaryFace68

section RelaxedSecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Homogeneous one-form coefficients under `2g < 3n` -/

/-! ## Packaged face and classification -/

end RelaxedSecondaryOneForms68

#print axioms firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius
#print axioms firstSecondaryFourThreeZero68_classify
#print axioms cubicLoadSPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadTPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadUPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadVPolynomial68_degreeBound_of_loadL
#print axioms cubicLoadTPolynomial68_degreeBound_of_loadL_alpha
#print axioms cubicLoadUPolynomial68_degreeBound_of_loadL_alpha
#print axioms cubicLoadVPolynomial68_degreeBound_of_loadL_alpha
#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
#print axioms secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
#print axioms cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
#print axioms cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
#print axioms polynomialSecondaryInvariantEquations68_of_loadL
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_of_loadL
#print axioms cubicLoadRowOnePolynomial68_degree_lt_of_loadL
#print axioms cubicLoadRowOnePolynomial68_degree_lt_of_loadL_alpha
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_of_loadL
#print axioms integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff_of_loadL_alpha
#print axioms integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL_alpha
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
#print axioms polynomialSecondaryFourThreeZeroEquations68_of_loadL

end Max11DegreeRoutes
