import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart04Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

theorem fiveRadiusReducedRowOnePolynomial68_coincidentSevenSplit
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e =
      fiveRadiusBalancedRowOneCore68 A B c d e +
        fiveRadiusCoincidentSevenRowOneTail68 gamma epsilon zeta A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusBalancedRowOneCore68, fiveRadiusBalancedRowOneTail68,
    fiveRadiusCoincidentSevenRowOneTail68]
  module

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
