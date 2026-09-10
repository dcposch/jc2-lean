import Grok810NonzeroFaceSplit4SpeedValChainScratch

/-! # `(8,10)` nonzero-face closure, split 5: compact-block clearing

Coordinator split of untracked `Grok810NonzeroFaceClosureScratch`
(SHA `be179b5c`).  No tracked file was edited.  The monolith is not
imported.

This piece holds `DegreeZeroCompactBlockClearing810`: each compact
block, after substituting the integer-cleared bars, equals its
expansion, discharged by rational-coefficient `ring`.  Isolated so a
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

set_option maxHeartbeats 64000000 in
/-- Rational-coefficient clearing proof for compact block `12`. -/
theorem nonzeroFace5SpeedT_block12_eq_expansion
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
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroCompactBlock12_810,
    degreeZeroCompactBlock12Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  ring

#print axioms nonzeroFace5SpeedT_block12_eq_expansion

set_option maxHeartbeats 64000000 in
/-- Rational-coefficient clearing proof for compact block `13`. -/
theorem nonzeroFace5SpeedT_block13_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock13_810
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
      degreeZeroCompactBlock13Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroCompactBlock13_810,
    degreeZeroCompactBlock13Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  ring

#print axioms nonzeroFace5SpeedT_block13_eq_expansion

set_option maxHeartbeats 64000000 in
/-- Rational-coefficient clearing proof for compact block `14`. -/
theorem nonzeroFace5SpeedT_block14_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock14_810
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
      degreeZeroCompactBlock14Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroCompactBlock14_810,
    degreeZeroCompactBlock14Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  ring

#print axioms nonzeroFace5SpeedT_block14_eq_expansion

set_option maxHeartbeats 64000000 in
/-- Rational-coefficient clearing proof for compact block `15`. -/
theorem nonzeroFace5SpeedT_block15_eq_expansion
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) :
    (degreeZeroCompactToSourceIntegerScale810 : F) *
      (degreeZeroCompactBlock15_810
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
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroCompactBlock15_810,
    degreeZeroCompactBlock15Expansion810,
    degreeZeroCompactToSourceIntegerScale810, degreeZeroLBar810, degreeZeroABar810, degreeZeroBBar810, degreeZeroCBar810, degreeZeroDBar810, degreeZeroEBar810, degreeZeroFBar810, degreeZeroGBar810, degreeZeroPBar810, degreeZeroQBar810, degreeZeroRBar810, degreeZeroSBar810, degreeZeroTBar810, degreeZeroUBar810, degreeZeroVBar810, degreeZeroWBar810]
  ring

#print axioms nonzeroFace5SpeedT_block15_eq_expansion

end DegreeZeroCompactBlockClearing810
end Max11DegreeRoutes
