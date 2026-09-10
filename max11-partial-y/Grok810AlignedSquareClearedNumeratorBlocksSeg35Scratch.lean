import Grok810AlignedSquareClearedNumeratorBlocksSeg34Scratch

/-! Part 35 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareSBar810_eq
    (h a7 b9 b8 b7 b6 b5 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (8192 : F) * h ^ 35 *
        depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
      alignedSquareSBar810 h a7 b8 b7 b6 b5 := by
  rw [depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 (0 : F) hh
    (by simpa using hN)]
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h8192, hh35]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareSBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
