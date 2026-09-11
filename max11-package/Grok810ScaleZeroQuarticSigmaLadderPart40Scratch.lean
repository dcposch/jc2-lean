import Grok810ScaleZeroQuarticSigmaLadderPart35Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart36Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart38Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart39Scratch

/-! Part 40 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticN2_810


def degreeZeroN2QuarticNoL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroN2QuarticNoL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroN2QuarticNoL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    degreeZeroN2QuarticNoL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroN2Quartic810_eq_l_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      n2QuarticLFace810 l A +
        degreeZeroN2QuarticNoL810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810,
    degreeZeroKappaQuartic810, n2QuarticLFace810,
    degreeZeroN2QuarticNoL810, degreeZeroN2QuarticNoL1810, degreeZeroN2QuarticNoL2810, degreeZeroN2QuarticNoL3810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring


end QuarticN2_810
end Max11DegreeRoutes
end
