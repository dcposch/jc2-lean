import Grok810AlignedSquareClearedNumeratorBlocksSeg40Scratch

/-! Part 89 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareCompactBlockClearing810

variable {F : Type*} [Field F] [CharZero F]


theorem alignedSquareCompactBlock0_of_L_zero
    (A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    alignedSquareCompactBlock0_810 (0 : F) A B C0 D0 E0 F0
        G0 P Q R S0 T0 U0 V0 W0 = 0 := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock0_810]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
