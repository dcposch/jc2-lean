import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Fable610ScaleZeroTwelfthDefectSpeedTPart03Scratch
import Sol610ScaleTwoDegreeZeroLocalPoleScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section LinearDvdAndPoleFive610

variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
/-- Cancel one polynomial power of a linear clearing. -/
theorem algebraMap_cancel_one_clearing_610
    (h old new : k[X]) (A : RatFunc k) (r : ℕ) (hh : h ≠ 0)
    (hfact : old = h * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h) ^ (r + 1) * A) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h) ^ r * A := by
  let hR : RatFunc k := algebraMap k[X] (RatFunc k) h
  have hhR : hR ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hfact
  apply mul_left_cancel₀ hhR
  calc
    hR * algebraMap k[X] (RatFunc k) new =
        algebraMap k[X] (RatFunc k) old := by
      dsimp only [hR]
      simpa only [map_mul] using hmapped.symm
    _ = hR ^ (r + 1) * A := hclear
    _ = hR * (hR ^ r * A) := by
      rw [add_comm r 1, pow_add, pow_one]
      ring

end LinearDvdAndPoleFive610

end Max11DegreeRoutes
