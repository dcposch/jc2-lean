import Fable610ScaleTwoAlignedSixthFaceScratch
import Fable610ScaleTwoAlignedFlatDefectPart03Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart03Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the sixth aligned defect; each block has at most six monomials. -/
private theorem memory610_flatSixthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b4, b5, b6, b7, Polynomial.C κ]
      [(174960 : K[X]), (15552 : K[X]), (-104976 : K[X]), (-29160 : K[X]), (-58320 : K[X]), (-145800 : K[X])]
      [[15, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [12, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [12, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b4, b5, b6, b7, Polynomial.C κ]
      [(-25920 : K[X]), (-12960 : K[X]), (122472 : K[X]), (104976 : K[X]), (87480 : K[X]), (29160 : K[X])]
      [[11, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
        [11, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1],
        [10, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0],
        [10, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
        [9, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b4, b5, b6, b7, Polynomial.C κ]
      [(-48600 : K[X]), (-64800 : K[X]), (34560 : K[X]), (-204120 : K[X]), (-87480 : K[X]), (-21600 : K[X])]
      [[9, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1],
        [7, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
        [7, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0],
        [6, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b4, b5, b6, b7, Polynomial.C κ]
      [(324000 : K[X]), (-10560 : K[X]), (90720 : K[X]), (-144000 : K[X]), (8800 : K[X])]
      [[6, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
        [5, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1],
        [4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0]] := by
  simp only [alignedSixthDefect610, memory610_flatThirdDefect, memory610_flatFourthDefect, memory610_flatFifthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
