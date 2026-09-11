import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorE610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 : K[X]) : K[X] :=
  (16384 : K[X]) * (177147 : K[X]) * H ^ 18 *
    ((2 : K[X]) * a0 * a4 + (2 : K[X]) * a1 * a3 + a2 ^ 2)

end Max11DegreeRoutes
