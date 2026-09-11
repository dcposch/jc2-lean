import Grok810AlignedSquareClearedNumeratorBlocksSeg13Scratch

/-! Part 29 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareBarEq810

variable {F : Type*} [Field F] [CharZero F]


theorem alignedSquareEBar810_eq
    (h a7 a6 a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    (65536 : F) * h ^ 42 *
        depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 =
      alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 := by
  rw [depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh]
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  field_simp [hh, h65536, hh42]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareEBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
