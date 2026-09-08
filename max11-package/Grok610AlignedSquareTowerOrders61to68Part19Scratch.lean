import Grok610AlignedSquareTowerOrders61to68Part18Scratch

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

/-- Cancel one polynomial power of a linear clearing. -/
theorem alignedSquare_algebraMap_cancel_one_clearing610
    (h0 old new : k[X]) (rho : RatFunc k) (r : ℕ) (hh0 : h0 ≠ 0)
    (hfact : old = h0 * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
  alignedSquare_algebraMap_cancel_pow610 h0 new rho 1 r hh0
    (by
      have hclear' :
          algebraMap k[X] (RatFunc k) (h0 * new) =
            (algebraMap k[X] (RatFunc k) h0) ^ (1 + r) * rho := by
        simpa [hfact, add_comm r 1] using hclear
      simpa [pow_one] using hclear')

end AlignedSquareTowerDvd610

end Max11DegreeRoutes
