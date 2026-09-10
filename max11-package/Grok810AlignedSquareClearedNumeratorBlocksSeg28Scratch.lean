import Grok810AlignedSquareClearedNumeratorBlocksSeg27Scratch

/-! Part 28 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareDBar810_eq
    (h a7 a6 a5 a4 a3 : F) (hh : h ≠ 0) :
    (1024 : F) * h ^ 35 *
        depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
      alignedSquareDBar810 h a7 a6 a5 a4 a3 := by
  rw [depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh]
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h1024, hh35]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareDBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
