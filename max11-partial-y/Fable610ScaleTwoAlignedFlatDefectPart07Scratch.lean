import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Fable610ScaleTwoAlignedFlatDefectPart06Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory610_flatThirdDefect from Fable610ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory610_flatFourthDefect from Fable610ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory610_flatFifthDefect from Fable610ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory610_flatSixthDefect from Fable610ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory610_flatSeventhDefect from Fable610ScaleTwoAlignedFlatDefectPart05Scratch in
open private memory610_flatEighthDefect from Fable610ScaleTwoAlignedFlatDefectPart06Scratch in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the ninth aligned defect; each block has at most six monomials. -/
private theorem memory610_flatNinthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1632586752 : K[X]), (-3174474240 : K[X]), (-3174474240 : K[X]), (-282175488 : K[X]), (-282175488 : K[X]), (-282175488 : K[X])]
      [[22, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [21, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [21, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [20, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [20, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [20, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(1904684544 : K[X]), (1632586752 : K[X]), (1360488960 : K[X]), (1088391168 : K[X]), (816293376 : K[X]), (544195584 : K[X])]
      [[19, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [19, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [19, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [19, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [19, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [19, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2116316160 : K[X]), (2116316160 : K[X]), (-793618560 : K[X]), (1058158080 : K[X]), (2645395200 : K[X]), (1146337920 : K[X])]
      [[18, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [18, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(305690112 : K[X]), (611380224 : K[X]), (305690112 : K[X]), (305690112 : K[X]), (-2222131968 : K[X]), (-2222131968 : K[X])]
      [[17, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
        [17, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [17, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [17, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [16, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [16, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1904684544 : K[X]), (-1111065984 : K[X]), (-1904684544 : K[X]), (-1587237120 : K[X]), (-793618560 : K[X]), (-1269789696 : K[X])]
      [[16, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [16, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [16, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [16, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
        [16, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [16, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-476171136 : K[X]), (117573120 : K[X]), (2601305280 : K[X]), (-1984046400 : K[X]), (3439013760 : K[X]), (-1146337920 : K[X])]
      [[16, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0],
        [15, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [15, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(955281600 : K[X]), (-322672896 : K[X]), (-968018688 : K[X]), (-322672896 : K[X]), (2407309632 : K[X]), (4814619264 : K[X])]
      [[15, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [14, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1],
        [14, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [13, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2063408256 : K[X]), (802436544 : K[X]), (2063408256 : K[X]), (1719506880 : K[X]), (458535168 : K[X]), (-135331560 : K[X])]
      [[13, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
        [13, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [13, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [13, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0],
        [13, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0],
        [12, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2993215680 : K[X]), (923438880 : K[X]), (-6639207120 : K[X]), (-2420046720 : K[X]), (336117600 : K[X]), (672235200 : K[X])]
      [[12, 0, 0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2541049056 : K[X]), (-3811573584 : K[X]), (-2178042048 : K[X]), (-453758760 : K[X]), (151252920 : K[X]), (3352773060 : K[X])]
      [[10, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [10, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0],
        [10, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 0, 0, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(6789575520 : K[X]), (-347321520 : K[X]), (2646926100 : K[X]), (453758760 : K[X]), (-164557575 : K[X]), (-4453558200 : K[X])]
      [[9, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 0],
        [6, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(50995620 : K[X]), (-455859495 : K[X]), (940662450 : K[X]), (-49579075 : K[X])]
      [[5, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1],
        [4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedNinthDefect610, memory610_flatThirdDefect, memory610_flatFourthDefect, memory610_flatFifthDefect, memory610_flatSixthDefect, memory610_flatSeventhDefect, memory610_flatEighthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
