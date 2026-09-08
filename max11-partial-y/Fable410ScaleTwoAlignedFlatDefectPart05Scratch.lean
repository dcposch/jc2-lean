import Fable410ScaleTwoAlignedFlatDefectPart04Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory410_flatFifthDefect from Fable410ScaleTwoAlignedFlatDefectPart03Scratch in
open private memory410_flatSixthDefect from Fable410ScaleTwoAlignedFlatDefectPart04Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the seventh defect; each block has at most six monomials. -/
private theorem memory410_flatSeventhDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedSeventhDefect410 H a0 a1 a2 a3 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-143360 : K[X]), (-14336 : K[X]), (-14336 : K[X]), (-32768 : K[X]), (-215040 : K[X]), (35840 : K[X])]
      [[10, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1],
        [9, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [8, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0],
        [8, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-89600 : K[X]), (57344 : K[X]), (19712 : K[X]), (49152 : K[X]), (19712 : K[X]), (40960 : K[X])]
      [[8, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
        [7, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1],
        [7, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(32768 : K[X]), (-17920 : K[X]), (327040 : K[X]), (295680 : K[X]), (-100352 : K[X]), (-50176 : K[X])]
      [[7, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
        [6, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0],
        [6, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0],
        [5, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-24640 : K[X]), (-86016 : K[X]), (-35840 : K[X]), (33880 : K[X]), (-443520 : K[X]), (137984 : K[X])]
      [[5, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0],
        [4, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(5852 : K[X]), (39424 : K[X]), (69300 : K[X]), (-43120 : K[X]), (15675 : K[X])]
      [[3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0],
        [2, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedSeventhDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, memory410_flatSixthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatSeventhDefect

end Max11DegreeRoutes
