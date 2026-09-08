import Grok610ScaleZeroCubicADominantPart58Scratch
import Grok610ScaleZeroCubicADominantPart59Scratch

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

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBD610 A B C D E +
        degreeZeroKappaCubicNoSigmaBD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBD610, degreeZeroKappaCubicNoSigmaBD610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
