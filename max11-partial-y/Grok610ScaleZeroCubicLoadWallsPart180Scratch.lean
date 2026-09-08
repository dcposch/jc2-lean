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

section CubicLoadBCDEWallKills610

variable {k : Type*} [Field k] [CharZero k]

theorem CubicLoadSigmaConeBCDE610_A_ne
    {A B C D E : k[X]} (hcone : CubicLoadSigmaConeBCDE610 A B C D E) :
    A ≠ 0 := by
  intro h0
  have : A.natDegree = 0 := by simp [h0]
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
  omega

end CubicLoadBCDEWallKills610

end Max11DegreeRoutes
