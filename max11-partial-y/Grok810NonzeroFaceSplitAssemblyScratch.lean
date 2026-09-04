import Grok810NonzeroFaceSplit5Scratch

/-! # `(8,10)` nonzero-face closure, assembly: scaled `ρ`, linear-root False, exclusion

Coordinator split of untracked `Grok810NonzeroFaceClosureScratch`
(SHA `be179b5c`).  No tracked file was edited.  The monolith is not
imported.  Compact-block expansions, groups, and clearing live in
`Grok810NonzeroFaceSplit{1-5}Scratch`.

This piece holds `DegreeZeroSourceEqExpansion810`,
`DegreeZeroSourceRho810` (including
`degreeZeroClearedSource810_eq_scaledSourceRho`),
`DegreeZeroLeftJetIdentity810`,
`DegreeZeroAlgebraMapClearing810` (including
`degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet`),
`DegreeZeroLinearRootFalse810`, and `NonzeroFaceExclusion810`.
Final theorems are unchanged from the monolith:
`normalized810ScaleTwo_nonzeroFace_false` and
`planeKeller810NonzeroFaceExclusion_closed`.

**CLOSED:** `PlaneKeller810NonzeroFaceExclusion`.  No `sorry`, no new
axioms, no finite-root shortcut.
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

/-! ## Source numerator equals the grouped expansions -/

section DegreeZeroSourceEqExpansion810

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup0810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup0810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock0Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock1Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock2Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup0810, degreeZeroCompactBlock0Expansion810, degreeZeroCompactBlock1Expansion810, degreeZeroCompactBlock2Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup1810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup1810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock3Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock4Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock5Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup1810, degreeZeroCompactBlock3Expansion810, degreeZeroCompactBlock4Expansion810, degreeZeroCompactBlock5Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup2810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup2810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock6Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock7Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock8Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup2810, degreeZeroCompactBlock6Expansion810, degreeZeroCompactBlock7Expansion810, degreeZeroCompactBlock8Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup3810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup3810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock9Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock10Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock11Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup3810, degreeZeroCompactBlock9Expansion810, degreeZeroCompactBlock10Expansion810, degreeZeroCompactBlock11Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup4810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup4810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup4810, degreeZeroCompactBlock12Expansion810, degreeZeroCompactBlock13Expansion810, degreeZeroCompactBlock14Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup5810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup5810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup5810, degreeZeroCompactBlock15Expansion810, degreeZeroCompactBlock16Expansion810, degreeZeroCompactBlock17Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup6810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup6810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock18Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock19Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock20Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup6810, degreeZeroCompactBlock18Expansion810, degreeZeroCompactBlock19Expansion810, degreeZeroCompactBlock20Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup7810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup7810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock21Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock22Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock23Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroExpansionGroup7810, degreeZeroCompactBlock21Expansion810, degreeZeroCompactBlock22Expansion810, degreeZeroCompactBlock23Expansion810]
  ring

set_option maxHeartbeats 1600000000 in
/-- The `977`-term source is the sum of the eight expansion groups. -/
theorem degreeZeroClearedSource810_eq_sum_groups
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      degreeZeroExpansionGroup0810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup1810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup2810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup3810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup4810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup5810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup6810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroExpansionGroup7810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroClearedSource810, degreeZeroClearedSourceBlock0_810, degreeZeroClearedSourceBlock1_810, degreeZeroClearedSourceBlock2_810, degreeZeroClearedSourceBlock3_810, degreeZeroClearedSourceBlock4_810, degreeZeroClearedSourceBlock5_810, degreeZeroClearedSourceBlock6_810, degreeZeroClearedSourceBlock7_810, degreeZeroClearedSourceBlock8_810, degreeZeroClearedSourceBlock9_810, degreeZeroClearedSourceBlock10_810, degreeZeroClearedSourceBlock11_810, degreeZeroClearedSourceBlock12_810, degreeZeroClearedSourceBlock13_810, degreeZeroClearedSourceBlock14_810, degreeZeroClearedSourceBlock15_810, degreeZeroClearedSourceBlock16_810, degreeZeroClearedSourceBlock17_810, degreeZeroClearedSourceBlock18_810, degreeZeroClearedSourceBlock19_810, degreeZeroClearedSourceBlock20_810, degreeZeroClearedSourceBlock21_810, degreeZeroClearedSourceBlock22_810, degreeZeroClearedSourceBlock23_810, degreeZeroClearedSourceBlock24_810,
    degreeZeroExpansionGroup0810, degreeZeroExpansionGroup1810, degreeZeroExpansionGroup2810, degreeZeroExpansionGroup3810, degreeZeroExpansionGroup4810, degreeZeroExpansionGroup5810, degreeZeroExpansionGroup6810, degreeZeroExpansionGroup7810]
  ring

#print axioms degreeZeroClearedSource810_eq_sum_groups

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_eq_sum_expansions
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
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
  have hsrc :=
    degreeZeroClearedSource810_eq_sum_groups h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg0 := degreeZeroExpansionGroup0810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg1 := degreeZeroExpansionGroup1810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg2 := degreeZeroExpansionGroup2810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg3 := degreeZeroExpansionGroup3810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg4 := degreeZeroExpansionGroup4810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg5 := degreeZeroExpansionGroup5810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg6 := degreeZeroExpansionGroup6810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hg7 := degreeZeroExpansionGroup7810_eq h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  rw [hsrc, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7]
  ac_rfl

#print axioms degreeZeroClearedSource810_eq_sum_expansions

end DegreeZeroSourceEqExpansion810


/-! ## Field identity `source = 2^{34} · compact(bars)` then `2^{62} h^{119} ρ` -/

section DegreeZeroSourceRho810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_eq_scaledCompact
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
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
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda /
            67108864) := by
  have hsrc :=
    degreeZeroClearedSource810_eq_sum_expansions h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hexp :=
    degreeZeroCompact_eq_sum_expansions h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1 lambda
  rw [hsrc, ← hexp]

set_option maxHeartbeats 800000000 in
/-- Algebraic clearing of the degree-zero primitive against `h^{119}`
on the ninth-power face. -/
theorem degreeZeroClearedSource810_eq_scaledSourceRho
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    degreeZeroClearedSource810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 lambda =
      (degreeZeroClearedIntegerScale810 : F) *
        h ^ degreeZeroSourceClearingPower810 *
          sourceRhoResidual810 h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5
            b4 b3 b2 b1 := by
  have hcompact :=
    degreeZeroClearedSource810_eq_scaledCompact h a7 a6 a5 a4 a3 a2 a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
  have hL := degreeZeroScaledDepressedL810 h a7 b9 lambda hh hN
  have hA := degreeZeroScaledDepressedA810 h a7 a6 hh
  have hB := degreeZeroScaledDepressedB810 h a7 a6 a5 hh
  have hC := degreeZeroScaledDepressedC810 h a7 a6 a5 a4 hh
  have hD0 := degreeZeroScaledDepressedD810 h a7 a6 a5 a4 a3 hh
  have hE0 := degreeZeroScaledDepressedE810 h a7 a6 a5 a4 a3 a2 hh
  have hF0 := degreeZeroScaledDepressedF810 h a7 a6 a5 a4 a3 a2 a1 hh
  have hG0 := degreeZeroScaledDepressedG810 h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP := degreeZeroScaledDepressedP810 h a7 b9 b8 lambda hh hN
  have hQ := degreeZeroScaledDepressedQ810 h a7 b9 b8 b7 lambda hh hN
  have hR := degreeZeroScaledDepressedR810 h a7 b9 b8 b7 b6 lambda hh hN
  have hS := degreeZeroScaledDepressedS810 h a7 b9 b8 b7 b6 b5 lambda hh
    hN
  have hT0 := degreeZeroScaledDepressedT810 h a7 b9 b8 b7 b6 b5 b4 lambda
    hh hN
  have hU0 := degreeZeroScaledDepressedU810 h a7 b9 b8 b7 b6 b5 b4 b3
    lambda hh hN
  have hV0 := degreeZeroScaledDepressedV810 h a7 b9 b8 b7 b6 b5 b4 b3 b2
    lambda hh hN
  have hW0 := degreeZeroScaledDepressedW810 h a7 b9 b8 b7 b6 b5 b4 b3 b2
    b1 lambda hh hN
  have hcoords :
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
          (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda /
            67108864) =
        degreeZeroClearedCompact810
          (h ^ 7 * depressedL810 h (octicDepressionR810 h a7) b9)
          (h ^ 14 * depressedA810 h (octicDepressionR810 h a7) a7 a6)
          (h ^ 21 * depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
          (h ^ 28 * depressedC810 h (octicDepressionR810 h a7) a7 a6 a5
            a4)
          (h ^ 35 * depressedD810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3)
          (h ^ 42 * depressedE810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2)
          (h ^ 49 * depressedF810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2 a1)
          (h ^ 56 * depressedG810 h (octicDepressionR810 h a7) a7 a6 a5
            a4 a3 a2 a1 a0)
          (h ^ 14 * depressedP810 h (octicDepressionR810 h a7) b9 b8)
          (h ^ 21 * depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
          (h ^ 28 * depressedR810 h (octicDepressionR810 h a7) b9 b8 b7
            b6)
          (h ^ 35 * depressedS810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5)
          (h ^ 42 * depressedT810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4)
          (h ^ 49 * depressedU810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3)
          (h ^ 56 * depressedV810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3 b2)
          (h ^ 63 * depressedW810 h (octicDepressionR810 h a7) b9 b8 b7
            b6 b5 b4 b3 b2 b1) := by
    simp only [degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810,
      degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810,
      degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810,
      degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810,
      degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810,
      degreeZeroWBar810]
    rw [hL, hA, hB, hC, hD0, hE0, hF0, hG0, hP, hQ, hR, hS, hT0, hU0,
      hV0, hW0]
  have hwt := degreeZeroClearedCompact810_weightedScale h
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
  have hrho := rhoResidual810_eq_clearedCompact
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
  have hscale :
      (degreeZeroCompactToSourceIntegerScale810 : F) *
          (degreeZeroGroupedIntegerScale810 : F) =
        (degreeZeroClearedIntegerScale810 : F) := by
    simp only [degreeZeroClearedIntegerScale810_eq_grouped_mul_compact,
      Nat.cast_mul]
    ring
  rw [hcompact, hcoords, hwt, hrho, sourceRhoResidual810]
  simp only [degreeZeroSourceClearingPower810]
  rw [← hscale]
  ac_rfl

#print axioms degreeZeroClearedSource810_eq_scaledCompact
#print axioms degreeZeroClearedSource810_eq_scaledSourceRho

end DegreeZeroSourceRho810
/-! ## Left-jet restriction and remaining-`17` clearing -/

section DegreeZeroLeftJetIdentity810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
theorem degreeZeroClearedSource810_leftJet_eq_scaledLeftJet
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0) :
    degreeZeroClearedSource810 h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3
        b2 b1 lambda =
      (degreeZeroClearedIntegerScale810 : F) *
        h ^ degreeZeroSourceClearingPower810 *
          sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 lambda := by
  have hN := degreeZeroLeftJet_ninthPower810 h t0 lambda
  have hsrc := degreeZeroClearedSource810_eq_scaledSourceRho h
    (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0
    ((5 * (h ^ 6 * t0) * h ^ 2 - lambda * h ^ 9) / 4)
    (h ^ 6 * s1) (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda hh hN
  simpa [sourceRhoResidualLeftJet810] using hsrc

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetQuotient810_eq_scaledLeftJet
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0) :
    degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      h ^ degreeZeroEffectiveTowerLength810 *
        ((degreeZeroClearedIntegerScale810 : F) *
          sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 lambda) := by
  have hfact := degreeZeroClearedSource810_leftJet_factored h t0 v1 u1
    a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda
  have hsrc := degreeZeroClearedSource810_leftJet_eq_scaledLeftJet h t0
    v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda hh
  have hhpow : h ^ degreeZeroSourceBaseOrder810 ≠ 0 :=
    pow_ne_zero degreeZeroSourceBaseOrder810 hh
  apply mul_left_cancel₀ hhpow
  calc
    h ^ degreeZeroSourceBaseOrder810 *
          degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
            w1 b62 b5 b4 b3 b2 b1 lambda =
        degreeZeroClearedSource810 h (h ^ 6 * t0) (h ^ 4 * v1)
          (h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)
          (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda := hfact.symm
    _ = (degreeZeroClearedIntegerScale810 : F) *
          h ^ degreeZeroSourceClearingPower810 *
            sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
              w1 b62 b5 b4 b3 b2 b1 lambda := hsrc
    _ = h ^ degreeZeroSourceBaseOrder810 *
          (h ^ degreeZeroEffectiveTowerLength810 *
            ((degreeZeroClearedIntegerScale810 : F) *
              sourceRhoResidualLeftJet810 h t0 v1 u1 a4 a3 a2 a1 a0 s1
                w1 b62 b5 b4 b3 b2 b1 lambda)) := by
      simp only [degreeZeroSourceBaseOrder810,
        degreeZeroEffectiveTowerLength810,
        degreeZeroSourceClearingPower810]
      ring

#print axioms degreeZeroClearedSource810_leftJet_eq_scaledLeftJet
#print axioms degreeZeroSourceJetQuotient810_eq_scaledLeftJet

end DegreeZeroLeftJetIdentity810

section DegreeZeroAlgebraMapClearing810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
theorem degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) (hh0 : h0 ≠ 0) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1
          w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
      (algebraMap k[X] (RatFunc k) h0) ^
          degreeZeroEffectiveTowerLength810 *
        ((degreeZeroClearedIntegerScale810 : RatFunc k) *
          sourceRhoResidualLeftJet810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) t0)
            (algebraMap k[X] (RatFunc k) v1)
            (algebraMap k[X] (RatFunc k) u1)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) s1)
            (algebraMap k[X] (RatFunc k) w1)
            (algebraMap k[X] (RatFunc k) b62)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRF : phi h0 ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hfield := degreeZeroSourceJetQuotient810_eq_scaledLeftJet
    (phi h0) (phi t0) (phi v1) (phi u1) (phi a4) (phi a3) (phi a2)
    (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5) (phi b4)
    (phi b3) (phi b2) (phi b1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroSourceJetQuotient810_map phi h0 t0 v1 u1 a4 a3
    a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)
  rw [hmap]
  simpa [phi, RatFunc.algebraMap_C] using hfield

#print axioms degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet

end DegreeZeroAlgebraMapClearing810
/-! ## Linear-root False and the nonzero-face exclusion -/

section DegreeZeroLinearRootFalse810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Source-facing contradiction at a linear root of `h₀`.  Clearing is
the block identity; the simple pole is the scaled left jet; the ceiling
is order `118`. -/
theorem degreeZeroFace810_linearRoot
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hj : j ≠ 0) : False := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, _hq9d, _hq6, _hsplit⟩ :=
    nonzeroFace810_linearRoot_fifteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have ha6 : p.coeff 6 = h0 ^ 4 * v1 := by
    rw [hv0, hv1]
    ring
  have ha5 : p.coeff 5 = h0 ^ 2 * u1 := by
    rw [hu0, hu1]
    ring
  have hb8 : q.coeff 8 = h0 ^ 6 * s1 := by
    rw [hs0, hs1]
    ring
  have hb7 : q.coeff 7 = h0 ^ 4 * w1 := by
    rw [hw0, hw1]
    ring
  have hclear :=
    degreeZeroSourceJetQuotient810_algebraMap_eq_pow_scaledLeftJet
      h0 t0 v1 u1 (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
      (p.coeff 0) s1 w1 b62 (q.coeff 5) (q.coeff 4) (q.coeff 3)
      (q.coeff 2) (q.coeff 1) lambda hh0
  have hderiv :=
    sourceRhoResidualLeftJet810_deriv_eq_simplePole_of_source p q H h0
      j lambda t0 v1 u1 s1 w1 b62 hp hq hh0 hH hp8 hq10 hN hD ht0 ha6
      ha5 hb8 hb7 hb62
  have hscale_ne : (degreeZeroClearedIntegerScale810 : k) ≠ 0 := by
    rw [degreeZeroClearedIntegerScale810_eq]
    norm_num
  exact degreeZeroFace810_linearRoot_order118Ceiling h0 t0 v1 u1
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) s1 w1
    b62 (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
    lambda ((degreeZeroClearedIntegerScale810 : k) * j) a hh0
    hh0degree hroot hclear hderiv (mul_ne_zero hscale_ne hj)

#print axioms degreeZeroFace810_linearRoot

end DegreeZeroLinearRootFalse810

section NonzeroFaceExclusion810

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial-level linear-root False implies the source-facing
nonzero-face exclusion. -/
theorem normalized810ScaleTwo_nonzeroFace_false :
    PlaneKeller810NonzeroFaceExclusion (K := K) :=
  normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse
    degreeZeroFace810_linearRoot

/-- **CLOSED.** The nonzero scale-two `(8,10)` first-face, in the
linear-root packet of `normalized810ScaleTwo_nonzeroFace_has_linear_root`. -/
theorem planeKeller810NonzeroFaceExclusion_closed :
    PlaneKeller810NonzeroFaceExclusion (K := K) :=
  normalized810ScaleTwo_nonzeroFace_false

#print axioms normalized810ScaleTwo_nonzeroFace_false
#print axioms planeKeller810NonzeroFaceExclusion_closed

end NonzeroFaceExclusion810

end Max11DegreeRoutes
