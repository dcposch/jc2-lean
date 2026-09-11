import Grok810AlignedSquareClearedNumeratorBlocksSeg10Scratch

/-! Part 26 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareBBar810_eq
    (h a7 a6 a5 : F) (hh : h ≠ 0) :
    (32 : F) * h ^ 21 *
        depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
      alignedSquareBBar810 h a7 a6 a5 := by
  rw [depressedB810_eq_cleared h a7 a6 a5 hh]
  have h32 : (32 : F) ≠ 0 := by norm_num
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  field_simp [hh, h32, hh21]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareBBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
