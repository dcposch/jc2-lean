import Grok810AlignedSquareClearedNumeratorBlocksSeg119Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg118BridgePart105Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg120Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg121Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg122Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg123Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg124Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg125Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg126Scratch
import Grok810AlignedSquareClearedNumeratorBlocksSeg127Scratch

/-! Part 116 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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
theorem alignedSquareCompactBlock23_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock23_810
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
      alignedSquareCompactBlock23Expansion810 h a7 a6 a5 a4 a3
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock23_810,
    alignedSquareCompactBlock23Expansion810,
    alignedSquareCompactToSourceIntegerScale810, alignedSquareABar810, alignedSquareBBar810, alignedSquareCBar810, alignedSquareDBar810, alignedSquareEBar810, alignedSquareFBar810, alignedSquareGBar810, alignedSquarePBar810, alignedSquareQBar810, alignedSquareRBar810, alignedSquareSBar810, alignedSquareTBar810, alignedSquareUBar810, alignedSquareVBar810, alignedSquareWBar810]
  field_simp [hh, h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
/-! Part 118 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareSourceEqExpansion810

variable {R : Type*} [CommRing R]


set_option maxHeartbeats 64000000 in
/-- The `λ = 0` source numerator is the sum of the 24 compact-block
expansions.  Each expansion is an integer polynomial; this is not the
977-term `field_simp` transport. -/
theorem alignedSquareClearedNumerator810_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareClearedNumerator810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 =
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
  simp only [alignedSquareClearedNumerator810, degreeZeroClearedSource810, alignedSquareCompactBlock0Expansion810, alignedSquareCompactBlock1Expansion810, alignedSquareCompactBlock2Expansion810, alignedSquareCompactBlock3Expansion810]
  rw [asqBand810Src0_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src1_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src2_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src3_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src4_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src5_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src6_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src7_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src8_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src9_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src10_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src11_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src12_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src13_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src14_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src15_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src16_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src17_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src18_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src19_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src20_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src21_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src22_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src23_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Src24_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1]
  rw [asqBand810Exp4_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp5_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp6_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp7_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp8_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1]
  rw [asqBand810Exp9_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp10_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp11_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp12_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp13_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1]
  rw [asqBand810Exp14_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp15_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp16_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp17_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp18_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1]
  rw [asqBand810Exp19_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp20_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp21_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp22_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1, asqBand810Exp23_split h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1]
  linear_combination asqBand810_band0 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band1 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band2 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band3 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band4 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band5 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band6 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band7 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 +
    asqBand810_band8 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1


end AlignedSquareSourceEqExpansion810
end Max11DegreeRoutes
end
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
/-! Part 92 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareCompactBlock1_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock1_810
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
      alignedSquareCompactBlock1Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock1_of_L_zero]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock1Expansion810]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
/-! Part 94 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareCompactBlock2_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock2_810
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
      alignedSquareCompactBlock2Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock2_of_L_zero]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock2Expansion810]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
/-! Part 96 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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


theorem alignedSquareCompactBlock3_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) :
    (alignedSquareCompactToSourceIntegerScale810 : F) *
      alignedSquareCompactBlock3_810
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
      alignedSquareCompactBlock3Expansion810 h a7 a6 a5 a4 a3
        a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  rw [alignedSquareCompactBlock3_of_L_zero]
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareCompactBlock3Expansion810]
  ring


end AlignedSquareCompactBlockClearing810
end Max11DegreeRoutes
end
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
