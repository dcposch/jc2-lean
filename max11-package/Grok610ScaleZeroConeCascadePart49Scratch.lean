import Grok610ScaleZeroConeCascadePart27Scratch
import Grok610ScaleZeroConeCascadePart28Scratch
import Grok610ScaleZeroConeCascadePart41Scratch
import Grok610ScaleZeroConeCascadePart42Scratch
import Grok610ScaleZeroConeCascadePart43Scratch
import Grok610ScaleZeroConeCascadePart44Scratch
import Grok610ScaleZeroConeCascadePart45Scratch
import Grok610ScaleZeroConeCascadePart46Scratch
import Grok610ScaleZeroConeCascadePart47Scratch
import Grok610ScaleZeroConeCascadePart48Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PrimitivePolynomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroPrimitivePolynomial610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0) =
      degreeZeroIntegratedPrimitive610 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroIntegratedPrimitive610, map_add, Polynomial.smul_eq_C_mul,
    map_mul, RatFunc.algebraMap_C,
    algebraMap_degreeZeroBaseGroupPolynomial610,
    algebraMap_degreeZeroAlphaGroupPolynomial610,
    algebraMap_degreeZeroBetaGroupPolynomial610,
    algebraMap_degreeZeroDeltaGroupPolynomial610,
    algebraMap_degreeZeroEpsilonGroupPolynomial610,
    algebraMap_degreeZeroZetaGroupPolynomial610,
    algebraMap_degreeZeroEtaGroupPolynomial610,
    algebraMap_degreeZeroThetaGroupPolynomial610]

end PrimitivePolynomial610

end Max11DegreeRoutes
