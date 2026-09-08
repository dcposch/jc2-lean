import Sol610ScaleTwoAlignedTwelfthDefectScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorJ610 {K : Type*} [CommRing K]
    (H a2 a3 a4 a5 : K[X]) : K[X] :=
  (576 : K[X]) * (
    (324 : K[X]) * H ^ 9 * a2 +
    (108 : K[X]) * H ^ 6 * a3 * a5 +
    (54 : K[X]) * H ^ 6 * a4 ^ 2 -
    (36 : K[X]) * H ^ 3 * a4 * a5 ^ 2 +
    (5 : K[X]) * a5 ^ 4)

end Max11DegreeRoutes
