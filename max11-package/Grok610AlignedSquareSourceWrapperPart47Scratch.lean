import Grok610AlignedSquareSourceWrapperPart43Scratch
import Grok610AlignedSquareSourceWrapperPart46Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareHeadKill610

variable {k : Type*} [Field k] [CharZero k]

/-- On `w₁ ≠ 0` the MixedPair base-order head forces `b₈ = 0`. -/
theorem alignedSquareBaseHead610_q8_of_w1_ne_zero
    (b8 w1 : k) (hw1 : w1 ≠ 0)
    (hhead : alignedSquareBaseHead610 b8 w1 = 0) :
    b8 = 0 := by
  have hcoeff : (67814496 : k) ≠ 0 :=
    alignedSquareBaseHeadCoeff610_ne_zero
  have hw13 : w1 ^ 13 ≠ 0 := pow_ne_zero 13 hw1
  have hassoc :
      (67814496 : k) * (b8 * w1 ^ 13) = 0 := by
    simpa [alignedSquareBaseHead610, mul_assoc] using hhead
  have hb8w : b8 * w1 ^ 13 = 0 :=
    (mul_eq_zero.mp hassoc).resolve_left hcoeff
  exact (mul_eq_zero.mp hb8w).resolve_right hw13

end AlignedSquareHeadKill610

end Max11DegreeRoutes
