import Grok610DegreeZeroOrder73Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSource610

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel three polynomial powers from a pole-six clearing. -/
theorem algebraMap_cancel_three_of_six_clearing610
    (h0 Q3 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ 3 * Q3) =
        (algebraMap k[X] (RatFunc k) h0) ^ 6 * rho) :
    algebraMap k[X] (RatFunc k) Q3 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero 3 hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ 3 * Q3) =
        hRF ^ 3 * algebraMap k[X] (RatFunc k) Q3 := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ 3 * algebraMap k[X] (RatFunc k) Q3 =
        algebraMap k[X] (RatFunc k) (h0 ^ 3 * Q3) := hmapPow.symm
    _ = hRF ^ 6 * rho := hquot
    _ = hRF ^ 3 * (hRF ^ 3 * rho) := by ring

end DegreeZeroOrderFiveSource610

end Max11DegreeRoutes
