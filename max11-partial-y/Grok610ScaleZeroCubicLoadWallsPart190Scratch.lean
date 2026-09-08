import Grok610ScaleZeroCubicLoadWallsPart07Scratch

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

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronCubicSigmaFaceCD610_coeff_top
    (A B C D E : k[X]) (hC : C ≠ 0) (hD : D ≠ 0) :
    (omicronCubicSigmaFaceCD610 A B C D E).coeff
        (C.natDegree + 2 * D.natDegree) =
      (-(5 / 27 : k)) * C.leadingCoeff * D.leadingCoeff ^ 2 := by
  simp only [omicronCubicSigmaFaceCD610, coeff_smul, smul_eq_mul]
  have hdeg : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hC (pow_ne_zero 2 hD), natDegree_pow]
  rw [← hdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  ring

end CubicLoadCDChamber610

end Max11DegreeRoutes
