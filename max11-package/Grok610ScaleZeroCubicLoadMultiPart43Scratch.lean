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

/-- On the CD cone, `2c+d ≤ a` forces the polynomial `B` to vanish. -/
theorem cubicLoadSigmaConeCD610_B_eq_zero_of_chamber
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree) :
    B = 0 := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hBcmp with hB0 | hBlt
  · exact hB0
  · have : 2 * C.natDegree ≤ A.natDegree :=
      le_trans (Nat.le_add_right _ _) hTle
    omega

end CubicLoadSigmaCDFinish610

end Max11DegreeRoutes
