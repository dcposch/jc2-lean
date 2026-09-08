import Sol610ScaleTwoAlignedTwelfthDefectScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorG610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 : K[X]) : K[X] :=
  (12288 : K[X]) * (
    (2187 : K[X]) * H ^ 15 * a0 +
    (1458 : K[X]) * H ^ 12 * a1 * a5 +
    (1458 : K[X]) * H ^ 12 * a2 * a4 +
    (729 : K[X]) * H ^ 12 * a3 ^ 2 -
    (243 : K[X]) * H ^ 9 * a2 * a5 ^ 2 -
    (486 : K[X]) * H ^ 9 * a3 * a4 * a5 -
    (81 : K[X]) * H ^ 9 * a4 ^ 3 +
    (108 : K[X]) * H ^ 6 * a3 * a5 ^ 3 +
    (162 : K[X]) * H ^ 6 * a4 ^ 2 * a5 ^ 2 -
    (63 : K[X]) * H ^ 3 * a4 * a5 ^ 4 +
    (7 : K[X]) * a5 ^ 6)

end Max11DegreeRoutes
