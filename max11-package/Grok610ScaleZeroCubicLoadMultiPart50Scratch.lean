import Grok610ScaleZeroCubicLoadMultiPart49Scratch

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

theorem lambdaCubicSigmaFaceCD610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) :
    (lambdaCubicSigmaFaceCD610 A B C D E).coeff
        (A.natDegree + 2 * D.natDegree) =
      (-(5 / 81 : k)) * lambdaCubicSigmaInnerCD610 A.leadingCoeff
        C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, heq, _⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  simp only [lambdaCubicSigmaFaceCD610, lambdaCubicSigmaInnerCD610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hdeg_AD2 : ((A * D ^ 2)).natDegree =
      A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AD2, hcf_C3]
  ring

end CubicLoadSigmaCDFinish610

end Max11DegreeRoutes
