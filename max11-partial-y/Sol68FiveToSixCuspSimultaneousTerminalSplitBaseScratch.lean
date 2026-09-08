import Sol68FiveToSixCuspLoadedLowerRowScratch

/-! # Simultaneous cusp wall and the first terminal coefficient

On `S = 7N-2G-S`, the first lower I3 coefficient is loaded by `d^2`.
The matching row-one coefficient then contradicts the all-nonzero cusp and
the two face equations.  Separately, the first unused terminal row-zero
coefficient is extracted directly from the exact constant-RHS equation;
it is not routed through the positive-coefficient adapter.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspSimultaneousTerminal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The first unused terminal coefficient, taken directly from the exact
constant RHS rather than the adapter's derived positive-coefficient field. -/
def FiveToSixTerminalDirectLowerRow68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 2) = 0


end FiveToSixCuspSimultaneousTerminal68

end Max11DegreeRoutes

