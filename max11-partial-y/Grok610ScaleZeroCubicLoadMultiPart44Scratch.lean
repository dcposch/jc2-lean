import Grok610ScaleZeroCubicLoadConesScratch
import Max11SpeedReflectDegLibScratch

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
set_option maxRecDepth 100000000

section CubicLoadSigmaCDFinish610

variable {k : Type*} [Field k] [CharZero k]

/-- Chamber `2c+d ≤ a` implies `7c ≤ 3a`. -/
theorem cubicLoadSigmaConeCD610_chamber_seven_c_le
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree) :
    7 * C.natDegree ≤ 3 * A.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  omega

end CubicLoadSigmaCDFinish610

end Max11DegreeRoutes
