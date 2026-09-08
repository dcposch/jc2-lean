import Grok610ScaleZeroCubicLoadMultiScratch
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

section CubicLoadWallFaces610

variable {k : Type*} [Field k] [CharZero k]

theorem n1CubicDeltaFace610_coeff_top (delta : k) (A : k[X]) :
    (n1CubicDeltaFace610 delta A).coeff (4 * A.natDegree) =
      (35 / 10368 * delta : k) * A.leadingCoeff ^ 4 := by
  simp only [n1CubicDeltaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
