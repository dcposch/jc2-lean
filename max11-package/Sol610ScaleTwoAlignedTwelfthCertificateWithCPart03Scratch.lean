import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorD610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (20316635136 : K[X]) * H ^ 21 * a0 * a3 +
  (20316635136 : K[X]) * H ^ 21 * a1 * a2 +
  (3386105856 : K[X]) * H ^ 18 * a0 * a4 * a5 +
  (3386105856 : K[X]) * H ^ 18 * a1 * a3 * a5 +
  (1693052928 : K[X]) * H ^ 18 * a1 * a4 ^ 2 +
  (1693052928 : K[X]) * H ^ 18 * a2 ^ 2 * a5 +
  (3386105856 : K[X]) * H ^ 18 * a2 * a3 * a4 +
  (564350976 : K[X]) * H ^ 18 * a3 ^ 3 -
  (470292480 : K[X]) * H ^ 15 * a0 * a5 ^ 3 -
  (1410877440 : K[X]) * H ^ 15 * a1 * a4 * a5 ^ 2 -
  (1410877440 : K[X]) * H ^ 15 * a2 * a3 * a5 ^ 2 -
  (1410877440 : K[X]) * H ^ 15 * a2 * a4 ^ 2 * a5 -
  (1410877440 : K[X]) * H ^ 15 * a3 ^ 2 * a4 * a5 -
  (470292480 : K[X]) * H ^ 15 * a3 * a4 ^ 3 +
  (215550720 : K[X]) * H ^ 12 * a1 * a5 ^ 4 +
  (862202880 : K[X]) * H ^ 12 * a2 * a4 * a5 ^ 3 +
  (431101440 : K[X]) * H ^ 12 * a3 ^ 2 * a5 ^ 3 +
  (1293304320 : K[X]) * H ^ 12 * a3 * a4 ^ 2 * a5 ^ 2 +
  (215550720 : K[X]) * H ^ 12 * a4 ^ 4 * a5 -
  (122145408 : K[X]) * H ^ 9 * a2 * a5 ^ 5 -
  (610727040 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 4 -
  (407151360 : K[X]) * H ^ 9 * a4 ^ 3 * a5 ^ 3 +
  (78037344 : K[X]) * H ^ 6 * a3 * a5 ^ 6 +
  (234112032 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 5 -
  (53882928 : K[X]) * H ^ 3 * a4 * a5 ^ 7 +
  (4365515 : K[X]) * a5 ^ 9

end Max11DegreeRoutes
