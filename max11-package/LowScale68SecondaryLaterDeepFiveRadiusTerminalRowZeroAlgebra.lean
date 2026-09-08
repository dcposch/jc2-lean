import LowScale68SecondaryLaterDeepFiveRadiusTerminalRowZeroAlgebraPart02Scratch

/-! # Terminal row-zero algebra on `2g = 5n`, `h = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalRowZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

#print axioms cubicLoadRowZeroPolynomial68_terminalEquality
#print axioms fiveRadiusTerminalRowZeroCore68_coeff
#print axioms fiveRadiusTerminalEqualityScalarSelector68_rowZero_impossible

end LaterDeepFiveRadiusTerminalRowZeroAlgebra68

end Max11DegreeRoutes
