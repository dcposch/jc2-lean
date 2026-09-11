import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorL610 {K : Type*} [CommRing K]
    (H a3 a4 a5 : K[X]) : K[X] :=
  (4 : K[X]) * ((216 : K[X]) * H ^ 6 * a3 +
    (36 : K[X]) * H ^ 3 * a4 * a5 - (5 : K[X]) * a5 ^ 3)

end Max11DegreeRoutes
