import Sol610ScaleTwoAlignedTwelfthDefectScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Polynomial multiplying the weight-five base row.  The factor `393216`
is `16384 * 24`, after clearing every CAS denominator. -/
def alignedTwelfthCofactorC610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (393216 : K[X]) * (
    (1062882 : K[X]) * H ^ 24 * a0 * a2 +
    (531441 : K[X]) * H ^ 24 * a1 ^ 2 -
    (1771470 : K[X]) * H ^ 21 * a0 * a3 * a5 -
    (885735 : K[X]) * H ^ 21 * a0 * a4 ^ 2 -
    (1771470 : K[X]) * H ^ 21 * a1 * a2 * a5 -
    (1771470 : K[X]) * H ^ 21 * a1 * a3 * a4 -
    (885735 : K[X]) * H ^ 21 * a2 ^ 2 * a4 -
    (885735 : K[X]) * H ^ 21 * a2 * a3 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a0 * a4 * a5 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a1 * a3 * a5 ^ 2 +
    (2361960 : K[X]) * H ^ 18 * a1 * a4 ^ 2 * a5 +
    (1180980 : K[X]) * H ^ 18 * a2 ^ 2 * a5 ^ 2 +
    (4723920 : K[X]) * H ^ 18 * a2 * a3 * a4 * a5 +
    (787320 : K[X]) * H ^ 18 * a2 * a4 ^ 3 +
    (787320 : K[X]) * H ^ 18 * a3 ^ 3 * a5 +
    (1180980 : K[X]) * H ^ 18 * a3 ^ 2 * a4 ^ 2 -
    (721710 : K[X]) * H ^ 15 * a0 * a5 ^ 4 -
    (2886840 : K[X]) * H ^ 15 * a1 * a4 * a5 ^ 3 -
    (2886840 : K[X]) * H ^ 15 * a2 * a3 * a5 ^ 3 -
    (4330260 : K[X]) * H ^ 15 * a2 * a4 ^ 2 * a5 ^ 2 -
    (4330260 : K[X]) * H ^ 15 * a3 ^ 2 * a4 * a5 ^ 2 -
    (2886840 : K[X]) * H ^ 15 * a3 * a4 ^ 3 * a5 -
    (144342 : K[X]) * H ^ 15 * a4 ^ 5 +
    (673596 : K[X]) * H ^ 12 * a1 * a5 ^ 5 +
    (3367980 : K[X]) * H ^ 12 * a2 * a4 * a5 ^ 4 +
    (1683990 : K[X]) * H ^ 12 * a3 ^ 2 * a5 ^ 4 +
    (6735960 : K[X]) * H ^ 12 * a3 * a4 ^ 2 * a5 ^ 3 +
    (1683990 : K[X]) * H ^ 12 * a4 ^ 4 * a5 ^ 2 -
    (636174 : K[X]) * H ^ 9 * a2 * a5 ^ 6 -
    (3817044 : K[X]) * H ^ 9 * a3 * a4 * a5 ^ 5 -
    (3180870 : K[X]) * H ^ 9 * a4 ^ 3 * a5 ^ 4 +
    (605880 : K[X]) * H ^ 6 * a3 * a5 ^ 7 +
    (2120580 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 6 -
    (580635 : K[X]) * H ^ 3 * a4 * a5 ^ 8 +
    (55913 : K[X]) * a5 ^ 10)

end Max11DegreeRoutes
