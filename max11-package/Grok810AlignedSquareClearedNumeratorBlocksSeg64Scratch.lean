import Grok810AlignedSquareClearedNumeratorBlocksSeg63Scratch

/-! Part 64 of 118 of `Grok810AlignedSquareClearedNumeratorBlocksScratch`, split so that no single module elaborates them all
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

section AlignedSquareCompactBlocks810

variable {K : Type*} [CommRing K]


/-- The 215-term compact is the sum of the 24 blocks. -/
theorem alignedSquareClearedCompact810_blockSum
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : K) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      alignedSquareCompactBlock0_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock1_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock2_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock3_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock4_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock5_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock6_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock7_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock8_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock9_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock10_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock11_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock12_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock13_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock14_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock15_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock16_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock17_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock18_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock19_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock20_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock21_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock22_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 +
      alignedSquareCompactBlock23_810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroClearedCompact810, alignedSquareCompactBlock0_810, alignedSquareCompactBlock1_810, alignedSquareCompactBlock2_810, alignedSquareCompactBlock3_810, alignedSquareCompactBlock4_810, alignedSquareCompactBlock5_810, alignedSquareCompactBlock6_810, alignedSquareCompactBlock7_810, alignedSquareCompactBlock8_810, alignedSquareCompactBlock9_810, alignedSquareCompactBlock10_810, alignedSquareCompactBlock11_810, alignedSquareCompactBlock12_810, alignedSquareCompactBlock13_810, alignedSquareCompactBlock14_810, alignedSquareCompactBlock15_810, alignedSquareCompactBlock16_810, alignedSquareCompactBlock17_810, alignedSquareCompactBlock18_810, alignedSquareCompactBlock19_810, alignedSquareCompactBlock20_810, alignedSquareCompactBlock21_810, alignedSquareCompactBlock22_810, alignedSquareCompactBlock23_810]
  ring


end AlignedSquareCompactBlocks810
end Max11DegreeRoutes
end
