import LowScale68SecondaryFirstLoadWallCorePart10Scratch

/-! # Literal coefficient cores on the `(6,8)` wall `2g = n`

This module checks the invariant and homogeneous one-form coefficients, the
pure `l` Jacobian cores, and the load-free row-one coefficient on the first
loaded equality wall.  The remaining bridge is the core-plus-remainder split
for the full row-two and row-zero load polynomials.
-/

noncomputable section

namespace Max11DegreeRoutes

/-! ## Polynomial coefficient extraction on `2g = n`

The formulas below re-prove the mixed leading coefficients of §3.3 by the
same `coeff_mul_at_bounds68` / `coeff_derivative_at_bound68` style as the
tracked first-face extraction.  Derivative substitutions are the coefficient
identity `(p').coeff(u-1) = u * p.coeff u`, which holds for constant
coordinates as well (both sides vanish).  On this wall every displayed
bound is positive: `2g = n` and `0 < n` force `n ≥ 2`. -/

section FirstLoadWallExtraction68

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ### Jacobian load cores, with the `A^5` cancellation checked by `ring` -/

end FirstLoadWallExtraction68

#print axioms cubicLoadRowTwoLCorePolynomial68_eq
#print axioms cubicLoadRowZeroLCorePolynomial68_eq
#print axioms cubicFirstIntegralFourPolynomial68_coeff_loadWall
#print axioms cubicFirstIntegralThreePolynomial68_coeff_loadWall
#print axioms cubicHomogeneousRowTwoPolynomial68_coeff_loadWall
#print axioms cubicHomogeneousRowZeroPolynomial68_coeff_loadWall
#print axioms integratedLowerRowOnePolynomial68_coeff_loadWall

end Max11DegreeRoutes
