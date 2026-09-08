import Fable410ScaleTwoAlignedEighthFacePart02Scratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the third defect; each block has at most six monomials. -/
private theorem memory410_flatThirdDefect {K : Type*} [CommRing K]
    (H a1 a2 a3 b7 : K[X]) (κ : K) :
    alignedThirdDefect410 H a1 a2 a3 b7 κ =
    Max11ReflectVal.polyR [H, a1, a2, a3, b7, Polynomial.C κ]
      [(40 : K[X]), (4 : K[X]), (60 : K[X]), (-16 : K[X]), (5 : K[X])]
      [[4, 1, 0, 0, 0, 0],
        [3, 0, 0, 1, 0, 1],
        [2, 0, 1, 1, 0, 0],
        [1, 0, 0, 0, 1, 0],
        [0, 0, 0, 3, 0, 0]] := by
  simp only [alignedThirdDefect410, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

#print axioms memory410_flatThirdDefect

end Max11DegreeRoutes
