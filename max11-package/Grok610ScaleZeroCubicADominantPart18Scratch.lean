import Grok610ScaleZeroCubicADominantPart17Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicN1_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_mu_add_A_kappa
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E +
        (1 / 6 : k) • (A * degreeZeroKappaCubic610 l alpha beta delta
          epsilon zeta eta theta A B C D E) := by
  simp only [degreeZeroN1Cubic610, degreeZeroMuCubic610,
    degreeZeroKappaCubic610]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

end CubicN1_610

end Max11DegreeRoutes
