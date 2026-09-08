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

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

theorem n2CubicSigmaFaceBCDE610_coeff_top_of_loadCone
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (n2CubicSigmaFaceBCDE610 A B C D E).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      (-(5 / 81 : k)) *
        n1CubicSigmaInnerBCDE610 A.leadingCoeff B.leadingCoeff
          C.leadingCoeff D.leadingCoeff E.leadingCoeff *
        A.leadingCoeff := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    _, _, _, _, heq1, heq2, heq3⟩
  simp only [n2CubicSigmaFaceBCDE610, n1CubicSigmaInnerBCDE610, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul]
  have hA2B2 : A ^ 2 * B ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hA2B2 hDne,
      natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne),
      natDegree_pow, natDegree_pow]
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hABC : A * B * C ≠ 0 :=
    mul_ne_zero (mul_ne_zero hAne hBne) hCne
  have hdeg_ABCE : ((A * B * C * E)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hABC hEne,
      natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCE : ((A * B * C * E)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff *
        E.leadingCoeff := by
    rw [← hdeg_ABCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_mul]
  have hAC2 : A * C ^ 2 ≠ 0 := mul_ne_zero hAne (pow_ne_zero 2 hCne)
  have hdeg_AC2D : ((A * C ^ 2 * D)).natDegree =
      2 * A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hAC2 hDne, natDegree_mul hAne (pow_ne_zero 2 hCne),
      natDegree_pow]
    omega
  have hcf_AC2D : ((A * C ^ 2 * D)).coeff
        (2 * A.natDegree + 2 * B.natDegree + D.natDegree) =
      A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_AC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  rw [hcf_A2B2D, hcf_ABCE, hcf_AC2D]
  ring

end CubicLoadWallSplits610

end Max11DegreeRoutes
