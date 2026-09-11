import Fable610ScaleTwoAlignedEighthFaceScratch
import Fable610ScaleTwoAlignedFlatDefectPart05Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory610_flatSixthDefect from Fable610ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory610_flatSeventhDefect from Fable610ScaleTwoAlignedFlatDefectPart05Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the eighth aligned defect; each block has at most six monomials. -/
private theorem memory610_flatEighthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2239488 : K[X]), (-15116544 : K[X]), (-33592320 : K[X]), (-16796160 : K[X]), (-2985984 : K[X]), (-2985984 : K[X])]
      [[20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [19, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [18, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [17, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
        [17, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1492992 : K[X]), (17635968 : K[X]), (15116544 : K[X]), (12597120 : K[X]), (10077696 : K[X]), (7558272 : K[X])]
      [[17, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [16, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [16, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [16, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [16, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
        [16, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-16796160 : K[X]), (27993600 : K[X]), (-5598720 : K[X]), (16796160 : K[X]), (3483648 : K[X]), (6967296 : K[X])]
      [[15, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1],
        [14, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(1161216 : K[X]), (-23514624 : K[X]), (-23514624 : K[X]), (-20155392 : K[X]), (-10077696 : K[X]), (-16796160 : K[X])]
      [[14, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
        [13, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [13, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
        [13, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
        [13, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-6718464 : K[X]), (311040 : K[X]), (24261120 : K[X]), (-13996800 : K[X]), (32659200 : K[X]), (6531840 : K[X])]
      [[13, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0],
        [12, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-3870720 : K[X]), (-5806080 : K[X]), (27433728 : K[X]), (27433728 : K[X]), (23514624 : K[X]), (6531840 : K[X])]
      [[11, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1],
        [10, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0],
        [10, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-725760 : K[X]), (-30481920 : K[X]), (-52254720 : K[X]), (4193280 : K[X]), (-30481920 : K[X]), (-6531840 : K[X])]
      [[9, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(1088640 : K[X]), (49593600 : K[X]), (-745472 : K[X]), (6604416 : K[X]), (-12579840 : K[X]), (698880 : K[X])]
      [[6, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0],
        [5, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1],
        [4, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedEighthDefect610, memory610_flatThirdDefect, memory610_flatFourthDefect, memory610_flatFifthDefect, memory610_flatSixthDefect, memory610_flatSeventhDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
