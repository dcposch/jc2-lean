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

/-- Named `h^3` coefficient on the `w₁` peel, forced if it is
the remaining pole-`11` head after cancelling `h₀^10`. -/
theorem alignedSquareW1PeelOrder64610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 11) * rho := by
    have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a)) 10 11 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
