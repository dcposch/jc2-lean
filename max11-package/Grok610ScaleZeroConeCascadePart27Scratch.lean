import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

/-- Integrated weight-fifteen primitive after the triangular residuals are
ground constants. -/
def degreeZeroIntegratedPrimitive610
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 alpha beta delta epsilon zeta eta theta : F) : F :=
  degreeZeroBaseGroup610 L A B C0 D0 E0 +
    alpha * degreeZeroAlphaGroup610 A B C0 D0 E0 +
    beta * degreeZeroBetaGroup610 A B C0 D0 E0 +
    delta * degreeZeroDeltaGroup610 A B C0 D0 +
    epsilon * degreeZeroEpsilonGroup610 A B C0 D0 +
    zeta * degreeZeroZetaGroup610 A B C0 D0 +
    eta * degreeZeroEtaGroup610 A B C0 D0 +
    theta * degreeZeroThetaGroup610 A B C0 E0

end PrimitivePolynomial610

end Max11DegreeRoutes
