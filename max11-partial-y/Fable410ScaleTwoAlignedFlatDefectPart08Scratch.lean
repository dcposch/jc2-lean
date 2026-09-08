import Fable410ScaleTwoAlignedNinthFacePart02Scratch
import Fable410ScaleTwoAlignedFlatDefectPart07Scratch
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
open private memory410_flatNinthDefect from Fable410ScaleTwoAlignedFlatDefectPart07Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the tenth defect; each block has at most six monomials. -/
private theorem memory410_flatTenthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedTenthDefect410 H a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-524288 : K[X]), (-4194304 : K[X]), (10485760 : K[X]), (2097152 : K[X]), (1048576 : K[X]), (4194304 : K[X])]
      [[15, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [15, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [14, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [13, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(1048576 : K[X]), (3145728 : K[X]), (2097152 : K[X]), (1048576 : K[X]), (26214400 : K[X]), (10485760 : K[X])]
      [[13, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [13, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [13, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [13, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [12, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2621440 : K[X]), (5242880 : K[X]), (-7340032 : K[X]), (-3145728 : K[X]), (-6291456 : K[X]), (-5242880 : K[X])]
      [[12, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [12, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [11, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [11, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [11, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1572864 : K[X]), (-3145728 : K[X]), (-3145728 : K[X]), (-5242880 : K[X]), (-4194304 : K[X]), (-262144 : K[X])]
      [[11, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [11, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [11, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [11, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [11, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2097152 : K[X]), (-3145728 : K[X]), (-1048576 : K[X]), (2621440 : K[X]), (-55050240 : K[X]), (-23592960 : K[X])]
      [[11, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [11, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [11, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [10, 1, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-44564480 : K[X]), (-3145728 : K[X]), (14680064 : K[X]), (1048576 : K[X]), (6291456 : K[X]), (7340032 : K[X])]
      [[10, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [10, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [9, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(7340032 : K[X]), (4194304 : K[X]), (12582912 : K[X]), (5242880 : K[X]), (2097152 : K[X]), (2097152 : K[X])]
      [[9, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [9, 0, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [9, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [9, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(5242880 : K[X]), (4194304 : K[X]), (1048576 : K[X]), (15728640 : K[X]), (-2621440 : K[X]), (73400320 : K[X])]
      [[9, 0, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [9, 0, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [9, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [8, 1, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [8, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(35389440 : K[X]), (-7340032 : K[X]), (-22020096 : K[X]), (-1048576 : K[X]), (-6291456 : K[X]), (-7340032 : K[X])]
      [[8, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [7, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [7, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2621440 : K[X]), (-9437184 : K[X]), (-5242880 : K[X]), (-1048576 : K[X]), (2621440 : K[X]), (-13107200 : K[X])]
      [[7, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [7, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [7, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [6, 1, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [6, 0, 1, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-47185920 : K[X]), (7340032 : K[X]), (14680064 : K[X]), (1048576 : K[X]), (6291456 : K[X]), (1048576 : K[X])]
      [[6, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [5, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-2621440 : K[X]), (15728640 : K[X]), (-7340032 : K[X]), (-131072 : K[X]), (-1048576 : K[X]), (1048576 : K[X])]
      [[4, 0, 1, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [4, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [1, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b0, b1, b2, b3, b4, b5, b6, b7, Polynomial.C κ]
      [(-393216 : K[X])]
      [[0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by
  simp only [alignedTenthDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, memory410_flatSixthDefect, memory410_flatSeventhDefect, memory410_flatEighthDefect, memory410_flatNinthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatTenthDefect

end Max11DegreeRoutes
