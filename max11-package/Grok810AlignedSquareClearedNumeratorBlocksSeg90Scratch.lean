import Grok810AlignedSquareClearedNumeratorBlocksSeg89Scratch

/-! Part 90 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareCompactBlock0_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock0_810
        (0 : F)
        (alignedSquareABar810 h a7 a6 / 16)
        (alignedSquareBBar810 h a7 a6 a5 / 32)
        (alignedSquareCBar810 h a7 a6 a5 a4 / 2048)
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / 1024)
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
        (alignedSquarePBar810 h a7 b8 / 64)
        (alignedSquareQBar810 h a7 b8 b7 / 64)
        (alignedSquareRBar810 h a7 b8 b7 b6 / 2048)
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / 8192)
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 / 131072)
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 / 262144)
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 / 16777216)
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864) =
      alignedSquareCompactBlock0Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock0_of_L_zero]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock0Expansion810]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
