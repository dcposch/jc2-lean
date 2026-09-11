import Grok810DegreeZeroSourceNumeratorScratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg01Scratch

/-! Part 4 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareClearedIntegerScale810_eq_grouped_mul :
    degreeZeroClearedIntegerScale810 =
      degreeZeroGroupedIntegerScale810 *
        alignedSquareCompactToSourceIntegerScale810 :=
  rfl


end Max11DegreeRoutes
end
