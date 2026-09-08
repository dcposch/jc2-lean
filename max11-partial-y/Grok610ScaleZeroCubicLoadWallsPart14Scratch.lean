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

theorem n1CubicZetaFace610_coeff_top (zeta : k) (A : k[X]) :
    (n1CubicZetaFace610 zeta A).coeff (3 * A.natDegree) =
      (5 / 432 * zeta : k) * A.leadingCoeff ^ 3 := by
  simp only [n1CubicZetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
