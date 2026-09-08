import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15mScratch

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem primitiveCubic_natDegree_le_zero_of_constants
    (l alpha beta delta epsilon zeta eta theta : k)
    {A B C D E : k[X]}
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0) :
    (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree ≤
      0 := by
  rw [eq_C_of_natDegree_eq_zero hA, eq_C_of_natDegree_eq_zero hB,
    eq_C_of_natDegree_eq_zero hC, eq_C_of_natDegree_eq_zero hD,
    eq_C_of_natDegree_eq_zero hE]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroPrimitiveCubic610, degreeZeroBaseGroupCubic610,
    degreeZeroAlphaGroupCubic610, degreeZeroBetaGroupCubic610,
    degreeZeroDeltaGroupCubic610, degreeZeroEpsilonGroupCubic610,
    degreeZeroZetaGroupCubic610, degreeZeroEtaGroupCubic610,
    degreeZeroThetaGroupCubic610, ← Polynomial.C_pow, ← Polynomial.C_mul,
    smul_C, ← Polynomial.C_add, ← Polynomial.C_sub, natDegree_C, le_refl]

end CubicKills610

end Max11DegreeRoutes

end
