import LowScale68SecondaryExtractionPart11Scratch

/-! # Extracting the first `(6,8)` secondary face

This module connects the abstract scalar face classified in
`LowScale68SecondaryFace` to the literal polynomial lower system.  The four
transverse coordinates have different secondary degree bounds, so the usual
single weighted-boundary lemmas are first replaced by arbitrary-bound
coefficient rules.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryExtraction68

variable {k : Type*} [Field k] [CharZero k]

end SecondaryExtraction68

#print axioms coeff_mul_at_bounds68
#print axioms coeff_mul_mul_at_bounds68
#print axioms coeff_pow_at_bound68
#print axioms firstIntegralFourPolynomial68_cubicCoordinates
#print axioms firstIntegralThreePolynomial68_cubicCoordinates
#print axioms cubicFirstIntegralFourPolynomial68_secondaryCoeff
#print axioms cubicFirstIntegralThreePolynomial68_secondaryCoeff
#print axioms firstSecondaryCoreRowTwoPolynomial68_coeff
#print axioms cubicHomogeneousRowTwoPolynomial68_secondaryCoeff
#print axioms cubicLoadPolynomials68_degreeBounds
#print axioms cubicLoadRowTwoPolynomial68_degree_lt
#print axioms integratedLowerRowTwoPolynomial68_secondaryCoeff
#print axioms polynomialSecondaryInvariantEquations68

end Max11DegreeRoutes
