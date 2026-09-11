import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorF610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (36 : K[X]) * (
    (5598720 : K[X]) * H ^ 15 * a0 * a5 +
    (5598720 : K[X]) * H ^ 15 * a1 * a4 +
    (5598720 : K[X]) * H ^ 15 * a2 * a3 -
    (466560 : K[X]) * H ^ 12 * a1 * a5 ^ 2 -
    (933120 : K[X]) * H ^ 12 * a2 * a4 * a5 -
    (466560 : K[X]) * H ^ 12 * a3 ^ 2 * a5 -
    (466560 : K[X]) * H ^ 12 * a3 * a4 ^ 2 +
    (181440 : K[X]) * H ^ 9 * a2 * a5 ^ 3 +
    (544320 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 2 +
    (181440 : K[X]) * H ^ 9 * a4 ^ 3 * a5 -
    (98280 : K[X]) * H ^ 6 * a3 * a5 ^ 4 -
    (196560 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 3 +
    (62244 : K[X]) * H ^ 3 * a4 * a5 ^ 5 -
    (6175 : K[X]) * a5 ^ 7)

end Max11DegreeRoutes
