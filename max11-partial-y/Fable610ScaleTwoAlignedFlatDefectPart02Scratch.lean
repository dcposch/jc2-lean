import Fable610ScaleTwoAlignedFourthFaceScratch
import Fable610ScaleTwoAlignedFlatDefectPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the fourth aligned defect; each block has at most six monomials. -/
private theorem memory610_flatFourthDefect {K : Type*} [CommRing K]
    (H a2 a3 a4 a5 b6 b7 : K[X]) (κ : K) :
    alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a2, a3, a4, a5, b6, b7, Polynomial.C κ]
      [(810 : K[X]), (72 : K[X]), (-486 : K[X]), (-405 : K[X]), (270 : K[X]), (-72 : K[X])]
      [[9, 1, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 1, 0, 0, 0, 1],
        [7, 0, 0, 0, 0, 1, 0, 0],
        [6, 0, 1, 0, 1, 0, 0, 0],
        [6, 0, 0, 2, 0, 0, 0, 0],
        [5, 0, 0, 0, 2, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a2, a3, a4, a5, b6, b7, Polynomial.C κ]
      [(567 : K[X]), (-720 : K[X]), (45 : K[X])]
      [[4, 0, 0, 0, 1, 0, 1, 0],
        [3, 0, 0, 1, 2, 0, 0, 0],
        [0, 0, 0, 0, 4, 0, 0, 0]] := by
  simp only [alignedFourthDefect610, memory610_flatThirdDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
