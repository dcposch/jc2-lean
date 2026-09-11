import Grok810AlignedSquareClearedNumeratorBlocksSeg64Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg90Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg92Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg94Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg96Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg97Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg98Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg99Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg100Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg101Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg102Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg103Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg104Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg105Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg106Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg107Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg108Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg109Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg110Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg111Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg112Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg113Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg114Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg115Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg116Scratch

/-! Part 117 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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
/-- Sum of the 24 compact-block expansions. -/
theorem alignedSquareCompact_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
        degreeZeroClearedCompact810
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
      alignedSquareCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
      alignedSquareCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  have hsum :=
    alignedSquareClearedCompact810_blockSum
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
      (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 / 67108864)
  have hb0 :=
    alignedSquareCompactBlock0_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb1 :=
    alignedSquareCompactBlock1_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb2 :=
    alignedSquareCompactBlock2_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb3 :=
    alignedSquareCompactBlock3_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb4 :=
    alignedSquareCompactBlock4_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb5 :=
    alignedSquareCompactBlock5_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb6 :=
    alignedSquareCompactBlock6_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb7 :=
    alignedSquareCompactBlock7_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb8 :=
    alignedSquareCompactBlock8_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb9 :=
    alignedSquareCompactBlock9_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb10 :=
    alignedSquareCompactBlock10_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb11 :=
    alignedSquareCompactBlock11_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb12 :=
    alignedSquareCompactBlock12_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb13 :=
    alignedSquareCompactBlock13_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb14 :=
    alignedSquareCompactBlock14_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb15 :=
    alignedSquareCompactBlock15_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb16 :=
    alignedSquareCompactBlock16_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb17 :=
    alignedSquareCompactBlock17_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb18 :=
    alignedSquareCompactBlock18_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb19 :=
    alignedSquareCompactBlock19_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb20 :=
    alignedSquareCompactBlock20_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb21 :=
    alignedSquareCompactBlock21_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb22 :=
    alignedSquareCompactBlock22_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  have hb23 :=
    alignedSquareCompactBlock23_eq_expansion h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 hh
  rw [hsum, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23]


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
