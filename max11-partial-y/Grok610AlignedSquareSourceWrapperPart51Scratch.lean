import Grok610AlignedSquareSourceWrapperPart47Scratch
import Grok610AlignedSquareSourceWrapperPart50Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareLocalPole610

variable {k : Type*} [Field k] [CharZero k]

/-- On `w₁(a) ≠ 0` the order-`21` obstruction forces `q₈(a) = 0`.
This is a new `q`-side peel, not a Keller collision. -/
theorem alignedSquare_poleTwentyOne_q8_eval_zero610
    (a j : k) (h0 Q : k[X]) (rho : RatFunc k)
    (w1 b8 : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hw1 : w1 ≠ 0)
    (hQ : Q.eval a = alignedSquareBaseHead610 b8 w1)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    b8 = 0 :=
  alignedSquareBaseHead610_q8_of_w1_ne_zero b8 w1 hw1
    (alignedSquare_poleTwentyOne_baseHead_eval_zero610 a j h0 Q rho w1
      b8 hdegree hroot hQ hclear hderiv)

end AlignedSquareLocalPole610

end Max11DegreeRoutes
