import Grok610ScaleZeroCubicConesScratch
import Grok610AlignedNonsquareDegreeZeroPrimitiveScratch

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

section CubicSigmaCones610

variable {k : Type*} [Field k] [CharZero k]

def CubicSigmaConeCE610 (A B C D E : k[X]) : Prop :=
  0 < A.natDegree
    ∧ 2 * B.natDegree < 3 * A.natDegree
    ∧ C.natDegree < 2 * A.natDegree
    ∧ 2 * D.natDegree < 5 * A.natDegree
    ∧ E.natDegree < 3 * A.natDegree
    ∧ 0 < C.natDegree
    ∧ 0 < E.natDegree
    ∧ 6 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * E.natDegree
    ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree
    ∧ A.natDegree + 2 * D.natDegree < 3 * C.natDegree
    ∧ 11 * A.natDegree < 6 * C.natDegree

end CubicSigmaCones610

end Max11DegreeRoutes
