import Grok810NonzeroFaceSplitAssemblySpeedValTrimSpeedSplitPart2Part01Scratch

/-! Part 2 of 2 of `Grok810NonzeroFaceSplitAssemblySpeedValTrimSpeedSplitPart2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
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

section DegreeZeroSourceEqExpansion810

variable {R : Type*} [CommRing R]


set_option maxHeartbeats 1600000000 in
theorem degreeZeroExpansionGroup5810_eq
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroExpansionGroup5810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda =
      degreeZeroCompactBlock15Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock16Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda +
      degreeZeroCompactBlock17Expansion810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda := by
  simp only [Max11ReflectVal.polyR_cons, Max11ReflectVal.monoR_cons, Max11ReflectVal.polyR_nil_left, Max11ReflectVal.polyR_nil_right, Max11ReflectVal.monoR_nil_left, Max11ReflectVal.monoR_nil_right, pow_zero, pow_one, one_mul, mul_one, degreeZeroExpansionGroup5810, degreeZeroCompactBlock15Expansion810, degreeZeroCompactBlock16Expansion810, degreeZeroCompactBlock17Expansion810]
  ring



end DegreeZeroSourceEqExpansion810
end Max11DegreeRoutes
end
