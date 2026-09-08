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

section CubicLoadSigmaBCEKill610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronCubicSigmaFaceBCE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hEne : E ≠ 0) :
    (omicronCubicSigmaFaceBCE610 A B C D E).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (1 / 81 : k) * omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, heq1, heq2, _⟩
  have htie : A.natDegree + 2 * B.natDegree = 2 * C.natDegree := by omega
  have htieE : 3 * A.natDegree + 6 * B.natDegree = 4 * E.natDegree := by omega
  simp only [omicronCubicSigmaFaceBCE610, omicronCubicSigmaInnerBCE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_C2E]
  ring

end CubicLoadSigmaBCEKill610

end Max11DegreeRoutes
