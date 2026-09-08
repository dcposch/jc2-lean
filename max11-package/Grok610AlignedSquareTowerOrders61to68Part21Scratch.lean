import Grok610AlignedSquareTowerOrders61to68Part02Scratch

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

section AlignedSquarePoleFourteen610

variable {k : Type*} [Field k] [CharZero k]

/-- Order-`14` specialisation matching the `w₁ = 0` remaining pole. -/
theorem alignedSquare_poleFourteen_head_eval_zero610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^
          alignedSquareW1ZeroRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  alignedSquare_localLinearPole_head_eval_zero610
    alignedSquareW1ZeroRemainingPole610 (by decide) a j h0 A0 rho
    hdegree hroot hclear hderiv

end AlignedSquarePoleFourteen610

end Max11DegreeRoutes
