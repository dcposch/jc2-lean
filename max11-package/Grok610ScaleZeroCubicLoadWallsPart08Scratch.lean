import Grok610ScaleZeroCubicLoadWallsPart01Scratch

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

theorem n2CubicBetaFace610_coeff_top (beta : k) (A : k[X]) :
    (n2CubicBetaFace610 beta A).coeff (6 * A.natDegree) =
      (35 / 41472 * beta : k) * A.leadingCoeff ^ 6 := by
  simp only [n2CubicBetaFace610, coeff_smul, smul_eq_mul]
  have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
  rw [← hAk, coeff_natDegree, leadingCoeff_pow]

end CubicLoadWallFaces610

end Max11DegreeRoutes
