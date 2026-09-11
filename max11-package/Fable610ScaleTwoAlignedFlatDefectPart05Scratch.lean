import Fable610ScaleTwoAlignedSeventhFaceScratch
import Fable610ScaleTwoAlignedFlatDefectPart04Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory610_flatSixthDefect from Fable610ScaleTwoAlignedFlatDefectPart04Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the seventh aligned defect; each block has at most six monomials. -/
private theorem memory610_flatSeventhDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(373248 : K[X]), (-2519424 : K[X]), (-699840 : K[X]), (-6298560 : K[X]), (-559872 : K[X]), (-559872 : K[X])]
      [[17, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [16, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [15, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1],
        [14, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2939328 : K[X]), (2519424 : K[X]), (2099520 : K[X]), (1679616 : K[X]), (291600 : K[X]), (-2099520 : K[X])]
      [[13, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [13, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [13, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
        [13, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
        [12, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(3149280 : K[X]), (-524880 : K[X]), (699840 : K[X]), (699840 : K[X]), (-4408992 : K[X]), (-2204496 : K[X])]
      [[12, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
        [11, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1],
        [11, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1],
        [10, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-3779136 : K[X]), (-1574640 : K[X]), (-174960 : K[X]), (3761640 : K[X]), (5248800 : K[X]), (-816480 : K[X])]
      [[10, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0],
        [10, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(5511240 : K[X]), (1574640 : K[X]), (54675 : K[X]), (-8748000 : K[X]), (183708 : K[X]), (-1607445 : K[X])]
      [[7, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0],
        [7, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0],
        [6, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0],
        [5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1],
        [4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2806650 : K[X]), (-164025 : K[X])]
      [[3, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedSeventhDefect610, memory610_flatThirdDefect, memory610_flatFourthDefect, memory610_flatFifthDefect, memory610_flatSixthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
