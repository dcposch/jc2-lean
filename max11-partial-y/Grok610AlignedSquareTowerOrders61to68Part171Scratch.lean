import Grok610AlignedSquareTowerOrders61to68Part212Scratch
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

set_option maxHeartbeats 1600000000 in
/-- Conditional order-`61` vanishing on `μ = 0` after the `q₈` peel.
If previous mixed orders have already supplied `h₀⁷ ∣` the substituted
jet — equivalently, if the order-`55`–`60` prefix has been peeled —
then cancelling those seven powers from the pole-`21` clearing leaves
a pole-`14` numerator whose head is the order-`61` mixed coefficient. -/
theorem alignedSquareMuZeroQ8Order61610_zero_of_pole_of_pow_seven
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q61 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61)
    (hhead :
      Q61.eval a =
        alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hfact] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  exact hhead.symm.trans hQ0

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
