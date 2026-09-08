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

/-- β-column of `N₁` is `7/6912 · β · A⁵`.  Competes when `6 Θ ≥ 3 ρ`. -/
def cubicLoadCompetesBeta610 (A B C D E : k[X]) : Prop :=
  CubicRatioConeA610 A B C D E ∧
    4 * A.natDegree ≥ 9 * B.natDegree ∧
    11 * A.natDegree ≥ 18 * C.natDegree ∧
    3 * A.natDegree ≥ 4 * D.natDegree ∧
    11 * A.natDegree ≥ 12 * E.natDegree

end CubicLoadB0_610

end Max11DegreeRoutes
