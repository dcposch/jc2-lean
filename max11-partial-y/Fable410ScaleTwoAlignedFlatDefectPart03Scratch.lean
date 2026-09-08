import Fable410ScaleTwoAlignedFlatDefectPart02Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
open private memory410_flatFourthDefect from Fable410ScaleTwoAlignedFlatDefectPart02Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the fifth defect; each block has at most six monomials. -/
private theorem memory410_flatFifthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b5 b6 b7 : K[X]) (κ : K) :
    alignedFifthDefect410 H a0 a1 a2 a3 b5 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b5, b6, b7, Polynomial.C κ]
      [(128 : K[X]), (-320 : K[X]), (-288 : K[X]), (-512 : K[X]), (120 : K[X]), (-4320 : K[X])]
      [[7, 0, 1, 0, 0, 0, 0, 0, 1],
        [6, 0, 1, 1, 0, 0, 0, 0, 0],
        [5, 0, 0, 1, 1, 0, 0, 0, 1],
        [5, 0, 0, 0, 0, 1, 0, 0, 0],
        [4, 0, 1, 0, 2, 0, 0, 0, 0],
        [4, 0, 0, 2, 1, 0, 0, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b5, b6, b7, Polynomial.C κ]
      [(896 : K[X]), (156 : K[X]), (768 : K[X]), (2700 : K[X]), (-1008 : K[X]), (351 : K[X])]
      [[3, 0, 0, 1, 0, 0, 0, 1, 0],
        [3, 0, 0, 0, 3, 0, 0, 0, 1],
        [3, 0, 0, 0, 1, 0, 1, 0, 0],
        [2, 0, 0, 1, 3, 0, 0, 0, 0],
        [1, 0, 0, 0, 2, 0, 0, 1, 0],
        [0, 0, 0, 0, 5, 0, 0, 0, 0]] := by
  simp only [alignedFifthDefect410, memory410_flatThirdDefect, memory410_flatFourthDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatFifthDefect

end Max11DegreeRoutes
