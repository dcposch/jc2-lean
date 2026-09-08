import Fable410ScaleTwoAlignedFlatDefectPart03Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
open private memory410_flatFifthDefect from Fable410ScaleTwoAlignedFlatDefectPart03Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the sixth defect; each block has at most six monomials. -/
private theorem memory410_flatSixthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b4 b5 b6 b7 : K[X]) (κ : K) :
    alignedSixthDefect410 H a0 a1 a2 a3 b4 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b4, b5, b6, b7, Polynomial.C κ]
      [(512 : K[X]), (-5120 : K[X]), (-1024 : K[X]), (-512 : K[X]), (-2048 : K[X]), (-12800 : K[X])]
      [[9, 1, 0, 0, 0, 0, 0, 0, 0, 1],
        [8, 0, 2, 0, 0, 0, 0, 0, 0, 0],
        [7, 0, 1, 0, 1, 0, 0, 0, 0, 1],
        [7, 0, 0, 2, 0, 0, 0, 0, 0, 1],
        [7, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [6, 0, 1, 1, 1, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b4, b5, b6, b7, Polynomial.C κ]
      [(-5120 : K[X]), (3584 : K[X]), (1536 : K[X]), (3072 : K[X]), (2560 : K[X]), (-1280 : K[X])]
      [[6, 0, 0, 3, 0, 0, 0, 0, 0, 0],
        [5, 0, 1, 0, 0, 0, 0, 0, 1, 0],
        [5, 0, 0, 1, 2, 0, 0, 0, 0, 1],
        [5, 0, 0, 1, 0, 0, 0, 1, 0, 0],
        [5, 0, 0, 0, 1, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 3, 0, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b4, b5, b6, b7, Polynomial.C κ]
      [(26880 : K[X]), (-7168 : K[X]), (-512 : K[X]), (-3072 : K[X]), (-7680 : K[X]), (3584 : K[X])]
      [[4, 0, 0, 2, 2, 0, 0, 0, 0, 0],
        [3, 0, 0, 1, 1, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 4, 0, 0, 0, 0, 1],
        [3, 0, 0, 0, 2, 0, 0, 1, 0, 0],
        [2, 0, 0, 1, 4, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 3, 0, 0, 0, 1, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b4, b5, b6, b7, Polynomial.C κ]
      [(-1280 : K[X])]
      [[0, 0, 0, 0, 6, 0, 0, 0, 0, 0]] := by
  simp only [alignedSixthDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, memory410_flatFifthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatSixthDefect

end Max11DegreeRoutes
