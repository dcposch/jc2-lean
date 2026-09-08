import Grok610ScaleZeroCubicADominantPart113Scratch
import Grok610ScaleZeroCubicADominantPart114Scratch

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

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceCD610 A B C D E +
        degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceCD610, degreeZeroLambdaCubicNoSigmaCD610]
  all_goals module

end CubicSigmaCD610

end Max11DegreeRoutes
