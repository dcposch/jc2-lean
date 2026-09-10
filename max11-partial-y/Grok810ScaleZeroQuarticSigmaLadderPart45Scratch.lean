import Grok810ScaleZeroQuarticSigmaLadderPart44Scratch

/-! Part 45 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

variable {k : Type*} [Field k] [CharZero k]

section QuarticKappaLadder810


def degreeZeroKappaQuarticNoL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroKappaQuarticNoL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroKappaQuarticNoL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuartic810_eq_l_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticLFace810 l A +
        degreeZeroKappaQuarticNoL810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticLFace810,
    degreeZeroKappaQuarticNoL810, degreeZeroKappaQuarticNoL1810, degreeZeroKappaQuarticNoL2810, degreeZeroKappaQuarticNoL3810, degreeZeroKappaQuarticNoL4810]
  module


end QuarticKappaLadder810
end Max11DegreeRoutes
end
