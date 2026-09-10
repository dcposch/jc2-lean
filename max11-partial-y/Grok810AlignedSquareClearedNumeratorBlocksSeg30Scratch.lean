import Grok810AlignedSquareClearedNumeratorBlocksSeg29Scratch

/-! Part 30 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareFBar810_eq
    (h a7 a6 a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    (131072 : F) * h ^ 49 *
        depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2
          a1 =
      alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 := by
  rw [depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh]
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  field_simp [hh, h131072, hh49]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareFBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
