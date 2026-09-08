import LowScale68SecondaryOneFormsPart11Scratch

/-! # The last two `(6,8)` secondary one-form equations

The preceding extraction module handles both invariants and the first
one-form row.  This module performs the same load-free/load decomposition for
the remaining two rows and connects their literal polynomial coefficients to
`F1` and `F0` of `FirstSecondaryFace68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

end SecondaryOneForms68

#print axioms cubicHomogeneousRowOnePolynomial68_eq_expanded
#print axioms firstSecondaryCoreRowOnePolynomial68_coeff
#print axioms cubicHomogeneousRowOnePolynomial68_secondaryCoeff
#print axioms cubicRowOnePolynomial68_split
#print axioms cubicLoadRowOnePolynomial68_degree_lt
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff
#print axioms cubicHomogeneousRowZeroPolynomial68_eq_expanded
#print axioms firstSecondaryCoreRowZeroPolynomial68_coeff
#print axioms cubicHomogeneousRowZeroPolynomial68_secondaryCoeff
#print axioms cubicRowZeroPolynomial68_split
#print axioms cubicLoadRowZeroPolynomial68_degree_lt
#print axioms integratedLowerRowZeroPolynomial68_secondaryCoeff
#print axioms integratedPolynomialLowerRows_secondaryEquations68
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68

end Max11DegreeRoutes
