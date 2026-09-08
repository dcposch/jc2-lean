import Fable410ScaleTwoAlignedFlatDefectPart01Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

open private memory410_flatThirdDefect from Fable410ScaleTwoAlignedFlatDefectPart01Scratch in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the fourth defect; each block has at most six monomials. -/
private theorem memory410_flatFourthDefect {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 b6 b7 : K[X]) (κ : K) :
    alignedFourthDefect410 H a0 a1 a2 a3 b6 b7 κ =
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b6, b7, Polynomial.C κ]
      [(320 : K[X]), (32 : K[X]), (-80 : K[X]), (240 : K[X]), (-40 : K[X]), (-128 : K[X])]
      [[6, 1, 0, 0, 0, 0, 0, 0],
        [5, 0, 0, 1, 0, 0, 0, 1],
        [4, 0, 1, 0, 1, 0, 0, 0],
        [4, 0, 0, 2, 0, 0, 0, 0],
        [3, 0, 0, 0, 2, 0, 0, 1],
        [3, 0, 0, 0, 0, 1, 0, 0]] +
    Max11ReflectVal.polyR [H, a0, a1, a2, a3, b6, b7, Polynomial.C κ]
      [(-720 : K[X]), (224 : K[X]), (-75 : K[X])]
      [[2, 0, 0, 1, 2, 0, 0, 0],
        [1, 0, 0, 0, 1, 0, 1, 0],
        [0, 0, 0, 0, 4, 0, 0, 0]] := by
  simp only [alignedFourthDefect410, memory410_flatThirdDefect, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatFourthDefect

end Max11DegreeRoutes
