import Sol610ScaleTwoAlignedTwelfthDefectScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

def alignedTwelfthCofactorOmega610 {K : Type*} [CommRing K]
    (H a4 : K[X]) : K[X] := (288 : K[X]) * H ^ 3 * a4

end Max11DegreeRoutes
