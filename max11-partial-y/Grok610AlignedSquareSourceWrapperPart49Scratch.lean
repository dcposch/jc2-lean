import Grok610AlignedSquareSourceWrapperPart48Scratch
import Grok610AlignedSquareSourceWrapperPart06Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareLocalPole610

variable {k : Type*} [Field k] [CharZero k]

/-- Order-`21` specialisation matching the MixedPair remaining pole. -/
theorem alignedSquare_poleTwentyOne_head_eval_zero610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  alignedSquare_localLinearPole_head_eval_zero610
    alignedSquareRemainingPole610 (by decide) a j h0 A0 rho hdegree
    hroot hclear hderiv

end AlignedSquareLocalPole610

end Max11DegreeRoutes
