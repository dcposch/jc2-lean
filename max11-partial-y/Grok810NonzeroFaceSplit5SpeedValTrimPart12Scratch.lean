import Grok810NonzeroFaceSplit4SpeedValChainScratch

/-! # Compact-block `12` clearing identity.

One declaration split out of `Grok810NonzeroFaceSplit5SpeedValTrimScratch`; the statement is byte-identical.
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
theorem degreeZeroCompactBlock12_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock12_810
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
        (degreeZeroWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 lambda / 67108864)) =
      degreeZeroCompactBlock12Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroCompactBlock12_810,
    degreeZeroCompactBlock12Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  field_simp [h2, h4, h8, h16, h32, h64, h1024, h2048, h8192, h65536, h131072, h262144, h16777216, h67108864, h17179869184]
  ring

end DegreeZeroCompactBlockClearing810
end Max11DegreeRoutes
