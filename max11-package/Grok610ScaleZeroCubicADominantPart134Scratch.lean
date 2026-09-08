import Grok610ScaleZeroCubicADominantPart17Scratch
import Grok610ScaleZeroCubicADominantPart132Scratch
import Grok610ScaleZeroCubicADominantPart133Scratch

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

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        degreeZeroN1CubicNoSigmaBCDE610 l alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610,
    degreeZeroN1CubicNoSigmaBCDE610]
  all_goals module

end CubicBalanced610

end Max11DegreeRoutes
