import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15nScratch

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in


theorem cubicCone_allConstant_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E) (j / t) hjdiv hder
  have hle :=
    primitiveCubic_natDegree_le_zero_of_constants l alpha beta delta
      epsilon zeta eta theta hA hB hC hD hE
  omega

end CubicKills610

end Max11DegreeRoutes

end
