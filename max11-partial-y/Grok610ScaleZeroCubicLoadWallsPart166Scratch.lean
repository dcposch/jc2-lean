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

section CubicLoadWallN1Tops610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCDE610_n1BetaTop_of_zetaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hwall : 9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  all_goals omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
