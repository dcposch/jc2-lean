import Fable610ScaleTwoAlignedFifthFaceScratch
import Fable610ScaleTwoAlignedFlatDefectPart02Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the fifth aligned defect; each block has at most six monomials. -/
private theorem memory610_flatFifthDefect {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 b5 b6 b7 : K[X]) (κ : K) :
    alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a1, a2, a3, a4, a5, b5, b6, b7, Polynomial.C κ]
      [(9720 : K[X]), (864 : K[X]), (-5832 : K[X]), (-3240 : K[X]), (-4860 : K[X]), (-1584 : K[X])]
      [[12, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 0, 0, 1, 0, 0, 0, 0, 0, 1],
        [10, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 1, 0, 0, 1, 0, 0, 0, 0],
        [9, 0, 0, 1, 1, 0, 0, 0, 0, 0],
        [8, 0, 0, 0, 1, 1, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a1, a2, a3, a4, a5, b5, b6, b7, Polynomial.C κ]
      [(6804 : K[X]), (5832 : K[X]), (2835 : K[X]), (-11880 : K[X]), (748 : K[X]), (-6237 : K[X])]
      [[7, 0, 0, 0, 1, 0, 0, 0, 1, 0],
        [7, 0, 0, 0, 0, 1, 0, 1, 0, 0],
        [6, 0, 0, 1, 0, 2, 0, 0, 0, 0],
        [6, 0, 0, 0, 2, 1, 0, 0, 0, 0],
        [5, 0, 0, 0, 0, 3, 0, 0, 0, 1],
        [4, 0, 0, 0, 0, 2, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a1, a2, a3, a4, a5, b5, b6, b7, Polynomial.C κ]
      [(8910 : K[X]), (-561 : K[X])]
      [[3, 0, 0, 0, 1, 3, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 5, 0, 0, 0, 0]] := by
  simp only [alignedFifthDefect610, memory610_flatThirdDefect, memory610_flatFourthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
