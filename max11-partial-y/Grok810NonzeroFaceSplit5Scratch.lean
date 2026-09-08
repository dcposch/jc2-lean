import Grok810NonzeroFaceSplit5SpeedValTrimSpeedSplitPart3Scratch

/-! # `(8,10)` nonzero-face closure, split 5: compact-block clearing

Coordinator split of untracked `Grok810NonzeroFaceClosureScratch`
(SHA `be179b5c`).  No tracked file was edited.  The monolith is not
imported.

This piece holds `DegreeZeroCompactBlockClearing810`: each compact
block, after substituting the integer-cleared bars, equals its
expansion, discharged by its own `field_simp; ring`.  Isolated so a
later failure does not recompile it.

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Block-by-block `2^{34} · compact(bars / integers)` -/

section DegreeZeroCompactBlockClearing810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Sum of the 24 compact-block expansions. -/
theorem degreeZeroCompact_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
        degreeZeroClearedCompact810
          (degreeZeroLBar810 h lambda / 4)
          (degreeZeroABar810 h a7 a6 / 16)
          (degreeZeroBBar810 h a7 a6 a5 / 32)
          (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
          (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
          (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
          (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
          (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
          (degreeZeroPBar810 h a7 b8 lambda / 64)
          (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
          (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
          (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
          (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
          (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
          (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864) =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  have hsum :=
    degreeZeroCompact810_blockSum
      (degreeZeroLBar810 h lambda / 4)
      (degreeZeroABar810 h a7 a6 / 16)
      (degreeZeroBBar810 h a7 a6 a5 / 32)
      (degreeZeroCBar810 h a7 a6 a5 a4 / 2048)
      (degreeZeroDBar810 h a7 a6 a5 a4 a3 / 1024)
      (degreeZeroEBar810 h a7 a6 a5 a4 a3 a2 / 65536)
      (degreeZeroFBar810 h a7 a6 a5 a4 a3 a2 a1 / 131072)
      (degreeZeroGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 / 16777216)
      (degreeZeroPBar810 h a7 b8 lambda / 64)
      (degreeZeroQBar810 h a7 b8 b7 lambda / 64)
      (degreeZeroRBar810 h a7 b8 b7 b6 lambda / 2048)
      (degreeZeroSBar810 h a7 b8 b7 b6 b5 lambda / 8192)
      (degreeZeroTBar810 h a7 b8 b7 b6 b5 b4 lambda / 131072)
      (degreeZeroUBar810 h a7 b8 b7 b6 b5 b4 b3 lambda / 262144)
      (degreeZeroVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 lambda / 16777216)
      (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)
  have hb0 :=
    degreeZeroCompactBlock0_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb1 :=
    degreeZeroCompactBlock1_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb2 :=
    degreeZeroCompactBlock2_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb3 :=
    degreeZeroCompactBlock3_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb4 :=
    degreeZeroCompactBlock4_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb5 :=
    degreeZeroCompactBlock5_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb6 :=
    degreeZeroCompactBlock6_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb7 :=
    degreeZeroCompactBlock7_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb8 :=
    degreeZeroCompactBlock8_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb9 :=
    degreeZeroCompactBlock9_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb10 :=
    degreeZeroCompactBlock10_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb11 :=
    degreeZeroCompactBlock11_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb12 :=
    degreeZeroCompactBlock12_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb13 :=
    degreeZeroCompactBlock13_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb14 :=
    degreeZeroCompactBlock14_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb15 :=
    degreeZeroCompactBlock15_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb16 :=
    degreeZeroCompactBlock16_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb17 :=
    degreeZeroCompactBlock17_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb18 :=
    degreeZeroCompactBlock18_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb19 :=
    degreeZeroCompactBlock19_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb20 :=
    degreeZeroCompactBlock20_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb21 :=
    degreeZeroCompactBlock21_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb22 :=
    degreeZeroCompactBlock22_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hb23 :=
    degreeZeroCompactBlock23_eq_expansion h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  rw [hsum, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23]

#print axioms degreeZeroCompact_eq_sum_expansions

end DegreeZeroCompactBlockClearing810
end Max11DegreeRoutes

