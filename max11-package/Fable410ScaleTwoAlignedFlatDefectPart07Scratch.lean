import Fable410ScaleTwoAlignedFlatDefectPart06Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory410_flatFifthDefect from Fable410ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory410_flatSixthDefect from Fable410ScaleTwoAlignedFlatDefectPart04Scratch in
open private memory410_flatSeventhDefect from Fable410ScaleTwoAlignedFlatDefectPart05Scratch in
open private memory410_flatEighthDefect from Fable410ScaleTwoAlignedFlatDefectPart06Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the ninth defect; each block has at most six monomials. -/
private theorem memory410_flatNinthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedNinthDefect410 H a0 a1 a2 a3 b1 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-327680 : K[X]), (-1048576 : K[X]), (819200 : K[X]), (1228800 : K[X]), (737280 : K[X]), (1310720 : K[X])]
      [[13, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [12, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(368640 : K[X]), (368640 : K[X]), (1048576 : K[X]), (786432 : K[X]), (524288 : K[X]), (-307200 : K[X])]
      [[11, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [11, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [11, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
        [10, 1, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(11059200 : K[X]), (3686400 : K[X]), (3379200 : K[X]), (-2293760 : K[X]), (-399360 : K[X]), (-1966080 : K[X])]
      [[10, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1146880 : K[X]), (-1198080 : K[X]), (-1966080 : K[X]), (-1638400 : K[X]), (-399360 : K[X]), (-819200 : K[X])]
      [[9, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1310720 : K[X]), (-491520 : K[X]), (-6912000 : K[X]), (537600 : K[X]), (-19929600 : K[X]), (-5990400 : K[X])]
      [[9, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
        [9, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0],
        [8, 1, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2580480 : K[X]), (5160960 : K[X]), (424320 : K[X]), (2211840 : K[X]), (860160 : K[X]), (848640 : K[X])]
      [[7, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(2211840 : K[X]), (1843200 : K[X]), (491520 : K[X]), (-898560 : K[X]), (6427200 : K[X]), (15225600 : K[X])]
      [[7, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0],
        [7, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0],
        [6, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2795520 : K[X]), (-4193280 : K[X]), (-445536 : K[X]), (-2396160 : K[X]), (-499200 : K[X]), (981240 : K[X])]
      [[5, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-7319520 : K[X]), (2970240 : K[X]), (66300 : K[X]), (509184 : K[X]), (278460 : K[X]), (-519792 : K[X])]
      [[4, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 0],
        [2, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(193375 : K[X])]
      [[0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedNinthDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, memory410_flatSixthDefect, memory410_flatSeventhDefect, memory410_flatEighthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatNinthDefect

end Max11DegreeRoutes
