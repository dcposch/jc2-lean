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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

/-- ζ-column of `N₁` is `5/432 · ζ · A³`.  Competes when `6 Θ ≥ 7 ρ`. -/
def cubicLoadCompetesZeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 21 * B.natDegree ∧
    11 * A.natDegree ≥ 42 * C.natDegree ∧
    9 * A.natDegree ≥ 28 * D.natDegree ∧
    11 * A.natDegree ≥ 28 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
