import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

open scoped Polynomial.Bivariate
noncomputable section
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

section CubicAllLettersZero610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem primitiveCubic_of_lettersBCDEzero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hB : B = 0) (hC : C = 0) (hD : D = 0) (hE : E = 0) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      (5 / 27648 * l : k) • A ^ 7 +
        (35 / 62208 * beta : k) • A ^ 6 +
        (1 / 576 * delta : k) • A ^ 5 +
        (1 / 192 * zeta : k) • A ^ 4 +
        (1 / 72 * theta : k) • A ^ 3 := by
  rw [hB, hC, hD, hE, degreeZeroPrimitiveCubic610_eq_flat]
  simp only [degreeZeroPrimitiveCubicFlat610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one, map_zero]
  ring

end CubicAllLettersZero610

end Max11DegreeRoutes
