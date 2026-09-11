import Grok610AlignedSquareSourceWrapperPart49Scratch
import Grok610AlignedSquareSourceWrapperPart44Scratch

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

/-- `w₁ = h₀ w₁n`: the specialised MixedPair jet is still a pole-`21`
numerator, so the parent obstruction applies.  After the polynomial
`h₀⁷` factor this vanishing is automatic; the order-`61` head uses the
remaining pole-`14` obstruction. -/
theorem alignedSquareW1Peel_jet_eval_zero_of_poleTwentyOne610
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1).eval a = 0 :=
  alignedSquare_poleTwentyOne_head_eval_zero610 a j h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    rho hdegree hroot hclear hderiv

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
