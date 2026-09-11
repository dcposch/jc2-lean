import Grok810SpeedValLibScratch
import Grok810DegreeZeroCompactBridgeScratch

/-! Part 7 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareCompactResidual810

variable {F : Type*} [Field F] [CharZero F]


/-- Exact numerical clearing from the grouped primitive to the compact
integer numerator.  Reuses the landed
`rhoResidual810_eq_clearedCompact`. -/
theorem alignedSquareClearedCompact810_eq_scaledRho
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      (degreeZeroGroupedIntegerScale810 : F) *
        rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 :=
  rhoResidual810_eq_clearedCompact L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0
    V0 W0


end AlignedSquareCompactResidual810
end Max11DegreeRoutes
end
