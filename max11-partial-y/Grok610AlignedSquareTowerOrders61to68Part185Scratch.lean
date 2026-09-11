import Grok610AlignedSquareTowerOrders61to68Part05Scratch
import Grok610AlignedSquareTowerOrders61to68Part212Scratch

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

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

theorem alignedSquareW1Complement_orders64to68_pow_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerBatchDivisibility610 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
        (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q64, Q65, Q66, Q67, Q68, hjet, _h64z, h65f, _h65z, h66f, _h66z,
      h67f, _h67z, h68f, _h68z, hdvd68⟩ :=
    alignedSquareW1Complement_orders64to68_remaining_dvd h0 w1n e1b e3b
      a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear
      hderiv
  obtain ⟨Q69, h69⟩ := hdvd68
  refine ⟨Q69, ?_⟩
  simp only [alignedSquareTowerBatchDivisibility610, hjet, h65f, h66f,
    h67f, h68f, h69]
  ring

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
