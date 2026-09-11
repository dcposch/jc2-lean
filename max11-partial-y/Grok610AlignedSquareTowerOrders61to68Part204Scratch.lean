import Grok610AlignedSquareSourceWrapperPart06Scratch
import Grok610AlignedSquareSourceWrapperPart44Scratch
import Grok610AlignedSquareTowerOrders61to68Part175Scratch
import Grok610AlignedSquareTowerOrders61to68Part26Scratch

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

theorem alignedSquareMuZeroQ8Order61610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (7 + 14) * rho := by
    have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a)) 7 14 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
