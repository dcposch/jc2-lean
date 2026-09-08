import Grok810AlignedSquareClearedNumeratorBlocksPart0Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart1Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart2Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart3Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart4Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart5Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart6Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart7Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart8Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart9Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart10Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart11Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart12Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart13Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart14Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart15Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart16Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart17Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart18Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart19Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart20Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart21Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart22Scratch
import Grok810AlignedSquareClearedNumeratorBlocksPart23Scratch

/-! # Sum of the 24 compact-block expansions.

Split out of `Grok810AlignedSquareClearedNumeratorBlocksScratch`.
-/

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

#print axioms alignedSquareCompact_eq_sum_expansions

end AlignedSquareCompactBlockClearing810


/-! ## Source numerator equals the sum of compact-block expansions -/

/-! ## Source numerator equals the sum of compact-block expansions -/

section AlignedSquareSourceEqExpansion810


variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, alignedSquareClearedNumerator810,
    degreeZeroClearedSource810, degreeZeroClearedSourceBlock0_810, degreeZeroClearedSourceBlock1_810, degreeZeroClearedSourceBlock2_810, degreeZeroClearedSourceBlock3_810, degreeZeroClearedSourceBlock4_810, degreeZeroClearedSourceBlock5_810, degreeZeroClearedSourceBlock6_810, degreeZeroClearedSourceBlock7_810, degreeZeroClearedSourceBlock8_810, degreeZeroClearedSourceBlock9_810, degreeZeroClearedSourceBlock10_810, degreeZeroClearedSourceBlock11_810, degreeZeroClearedSourceBlock12_810, degreeZeroClearedSourceBlock13_810, degreeZeroClearedSourceBlock14_810, degreeZeroClearedSourceBlock15_810, degreeZeroClearedSourceBlock16_810, degreeZeroClearedSourceBlock17_810, degreeZeroClearedSourceBlock18_810, degreeZeroClearedSourceBlock19_810, degreeZeroClearedSourceBlock20_810, degreeZeroClearedSourceBlock21_810, degreeZeroClearedSourceBlock22_810, degreeZeroClearedSourceBlock23_810, degreeZeroClearedSourceBlock24_810,
    alignedSquareCompactBlock0Expansion810, alignedSquareCompactBlock1Expansion810, alignedSquareCompactBlock2Expansion810, alignedSquareCompactBlock3Expansion810, alignedSquareCompactBlock4Expansion810, alignedSquareCompactBlock5Expansion810, alignedSquareCompactBlock6Expansion810, alignedSquareCompactBlock7Expansion810, alignedSquareCompactBlock8Expansion810, alignedSquareCompactBlock9Expansion810, alignedSquareCompactBlock10Expansion810, alignedSquareCompactBlock11Expansion810, alignedSquareCompactBlock12Expansion810, alignedSquareCompactBlock13Expansion810, alignedSquareCompactBlock14Expansion810, alignedSquareCompactBlock15Expansion810, alignedSquareCompactBlock16Expansion810, alignedSquareCompactBlock17Expansion810, alignedSquareCompactBlock18Expansion810, alignedSquareCompactBlock19Expansion810, alignedSquareCompactBlock20Expansion810, alignedSquareCompactBlock21Expansion810, alignedSquareCompactBlock22Expansion810, alignedSquareCompactBlock23Expansion810]
  ring

#print axioms alignedSquareClearedNumerator810_eq_sum_expansions


end AlignedSquareSourceEqExpansion810

/-! ## Field identity `N = 2^{62} h^{119} ρ` -/


end Max11DegreeRoutes
