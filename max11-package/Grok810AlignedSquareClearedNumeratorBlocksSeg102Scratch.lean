import Grok810AlignedSquareClearedNumeratorBlocksSeg01Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg09Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg10Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg11Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg12Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg13Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg14Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg15Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg16Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg17Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg18Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg19Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg20Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg21Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg22Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg23Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg49Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg74Scratch

/-! Part 102 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


set_option maxHeartbeats 800000000 in
theorem alignedSquareCompactBlock9_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock9_810
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
      alignedSquareCompactBlock9Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have h17179869184 : (17179869184 : F) ≠ 0 := by norm_num
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock9_810,
    alignedSquareCompactBlock9Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
