import Fable410ScaleTwoAlignedFlatDefectPart05Scratch
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the eighth defect; each block has at most six monomials. -/
private theorem memory410_flatEighthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedEighthDefect410 H a0 a1 a2 a3 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-245760 : K[X]), (-49152 : K[X]), (-24576 : K[X]), (-131072 : K[X]), (122880 : K[X]), (-368640 : K[X])]
      [[12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [10, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [10, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(122880 : K[X]), (61440 : K[X]), (196608 : K[X]), (122880 : K[X]), (163840 : K[X]), (20480 : K[X])]
      [[10, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1],
        [9, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(131072 : K[X]), (98304 : K[X]), (1105920 : K[X]), (-61440 : K[X]), (1689600 : K[X]), (230400 : K[X])]
      [[9, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
        [9, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
        [8, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-344064 : K[X]), (-344064 : K[X]), (-71680 : K[X]), (-294912 : K[X]), (-107520 : K[X]), (-147456 : K[X])]
      [[7, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-245760 : K[X]), (-98304 : K[X]), (115200 : K[X]), (-1203200 : K[X]), (-1843200 : K[X]), (430080 : K[X])]
      [[7, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0],
        [7, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0],
        [6, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0],
        [5, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(430080 : K[X]), (80640 : K[X]), (368640 : K[X]), (102400 : K[X]), (-147840 : K[X]), (1411200 : K[X])]
      [[5, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0],
        [4, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-501760 : K[X]), (-14784 : K[X]), (-107520 : K[X]), (-120960 : K[X]), (112896 : K[X]), (-41580 : K[X])]
      [[3, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0],
        [2, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedEighthDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, memory410_flatSixthDefect, memory410_flatSeventhDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatEighthDefect

end Max11DegreeRoutes
