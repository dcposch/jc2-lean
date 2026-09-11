import Grok810AlignedSquareClearedNumeratorBlocksSeg16Scratch

/-! Part 32 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquarePBar810_eq
    (h a7 b9 b8 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    (64 : F) * h ^ 14 *
        depressedP810 h (octicDepressionR810 h a7) b9 b8 =
      alignedSquarePBar810 h a7 b8 := by
  rw [depressedP810_eq_cleared_ninthPower h a7 b9 b8 (0 : F) hh
    (by simpa using hN)]
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  field_simp [hh, h64, hh14]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquarePBar810]
  ring


end AlignedSquareBarEq810
end Max11DegreeRoutes
end
