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

theorem cubicLoadSigmaConeCD610_n1BetaTop_of_deltaWall
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 30 * A.natDegree + 42 * C.natDegree) :
    cubicN1BetaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have h7c : 7 * C.natDegree = 9 * A.natDegree := by omega
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rcases hBcmp with hB0 | hBlt
    · have hBdeg : B.natDegree = 0 := by simp [hB0]
      rw [hBdeg]; omega
    · have : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree :=
        Nat.succ_le_of_lt hBlt
      omega
  · omega
  · omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadWallN1Tops610

end Max11DegreeRoutes
