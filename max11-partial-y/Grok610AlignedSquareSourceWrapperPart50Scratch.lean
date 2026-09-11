import Grok610AlignedSquareSourceWrapperPart43Scratch
import Grok610AlignedSquareSourceWrapperPart49Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareLocalPole610

variable {k : Type*} [Field k] [CharZero k]

/-- If the remaining order-`21` numerator is the MixedPair jet quotient,
the obstruction forces the base-order head to vanish at `a`. -/
theorem alignedSquare_poleTwentyOne_baseHead_eval_zero610
    (a j : k) (h0 Q : k[X]) (rho : RatFunc k)
    (w1 b8 : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hQ : Q.eval a = alignedSquareBaseHead610 b8 w1)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareBaseHead610 b8 w1 = 0 := by
  have hA0 :=
    alignedSquare_poleTwentyOne_head_eval_zero610 a j h0 Q rho hdegree
      hroot hclear hderiv
  exact hQ.symm.trans hA0

end AlignedSquareLocalPole610

end Max11DegreeRoutes
