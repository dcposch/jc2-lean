import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorI610 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (4374 : K[X]) * (
    (128 : K[X]) * H ^ 12 * a1 +
    (64 : K[X]) * H ^ 9 * a2 * a5 +
    (64 : K[X]) * H ^ 9 * a3 * a4 -
    (16 : K[X]) * H ^ 6 * a3 * a5 ^ 2 -
    (16 : K[X]) * H ^ 6 * a4 ^ 2 * a5 +
    (8 : K[X]) * H ^ 3 * a4 * a5 ^ 3 - a5 ^ 5)

end Max11DegreeRoutes
