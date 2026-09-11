import Fable610ScaleTwoAlignedThirdFaceScratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- Flat polynomial data for the third aligned defect; each block has at most six monomials. -/
private theorem memory610_flatThirdDefect {K : Type*} [CommRing K]
    (H a3 a4 a5 b7 : K[X]) (κ : K) :
    alignedThirdDefect610 H a3 a4 a5 b7 κ =
    Max11ReflectVal.polyR [H, a3, a4, a5, b7, Polynomial.C κ]
      [(135 : K[X]), (12 : K[X]), (-81 : K[X]), (90 : K[X]), (-5 : K[X])]
      [[6, 1, 0, 0, 0, 0],
        [5, 0, 0, 1, 0, 1],
        [4, 0, 0, 0, 1, 0],
        [3, 0, 1, 1, 0, 0],
        [0, 0, 0, 3, 0, 0]] := by
  simp only [alignedThirdDefect610, Max11ReflectVal.polyR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_cons, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, add_zero]
  ring

end Max11DegreeRoutes
