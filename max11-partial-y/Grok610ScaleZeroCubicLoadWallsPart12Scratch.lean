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

theorem n1CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n1CubicBetaFace610 beta A).coeff (5 * A.natDegree) =
      (7 / 6912 * beta : k) * A.leadingCoeff ^ 5 := by
  simp only [n1CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
