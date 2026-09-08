import Grok610AlignedSquareSourceWrapperScratch
import Grok610PoleCeilingLemmaScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section AlignedSquareTowerDvd610

variable {k : Type*} [Field k]

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing. -/
theorem alignedSquare_algebraMap_cancel_pow610
    (h0 Q : k[X]) (rho : RatFunc k) (m n : ℕ) (hh0 : h0 ≠ 0)
    (hclear :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho) :
    algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero m hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        hRF ^ m * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ m * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ m * Q) := hmapPow.symm
    _ = hRF ^ (m + n) * rho := hclear
    _ = hRF ^ m * (hRF ^ n * rho) := by
      rw [pow_add]
      ring

end AlignedSquareTowerDvd610

end Max11DegreeRoutes
