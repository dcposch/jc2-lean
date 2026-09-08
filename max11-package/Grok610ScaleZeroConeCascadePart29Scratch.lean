import Grok610ScaleZeroConeCascadePart14Scratch
import Grok610ScaleZeroConeCascadePart18Scratch
import Grok610ScaleZeroConeCascadePart19Scratch
import Grok610ScaleZeroConeCascadePart22Scratch
import Grok610ScaleZeroConeCascadePart23Scratch
import Grok610ScaleZeroConeCascadePart24Scratch
import Grok610ScaleZeroConeCascadePart25Scratch
import Grok610ScaleZeroConeCascadePart26Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

/-- Primitive with the unique-`A` face deleted. -/
def degreeZeroPrimitiveHighARest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighARest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

end PrimitivePolynomial610

end Max11DegreeRoutes
