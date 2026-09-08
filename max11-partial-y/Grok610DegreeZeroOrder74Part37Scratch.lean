import Grok610DegreeZeroOrder73Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- Cancel five polynomial powers from a pole-six clearing. -/
theorem algebraMap_cancel_five_of_six_clearing610
    (h0 Q5 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ 5 * Q5) =
        (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho) :
    algebraMap k[X] (RatFunc k) Q5 =
      (algebraMap k[X] (RatFunc k) h0) ^ 1 * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero 5 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ 5 * Q5) =
        hRF ^ 5 * algebraMap k[X] (RatFunc k) Q5 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ 5 * algebraMap k[X] (RatFunc k) Q5 =
        algebraMap k[X] (RatFunc k) (h0 ^ 5 * Q5) := hmapPow.symm
    _ = hRF ^ 6 * rho := hquot
    _ = hRF ^ 5 * (hRF ^ 1 * rho) := by ring

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
