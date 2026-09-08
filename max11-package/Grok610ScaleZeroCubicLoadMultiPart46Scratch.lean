import Grok610ScaleZeroCubicLoadMultiPart44Scratch

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

theorem cubicLoadSigmaConeCD610_chamber_n1DeltaTop
    {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hB0 : B = 0) :
    cubicN1DeltaTop610 A B C D E := by
  rcases hcone with ⟨hload, hCne, hDne, heq, hBcmp, hEcmp⟩
  rcases hload with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have h7 : 7 * C.natDegree ≤ 3 * A.natDegree :=
    cubicLoadSigmaConeCD610_chamber_seven_c_le
      ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, hCne, hDne, heq,
        hBcmp, hEcmp⟩ hTle
  have hBdeg : B.natDegree = 0 := by simp [hB0]
  refine ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hBdeg]; omega
  · omega
  · have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
    omega
  · rcases hEcmp with hE0 | hElt
    · have hEdeg : E.natDegree = 0 := by simp [hE0]
      rw [hEdeg]; omega
    · omega

end CubicLoadSigmaCDFinish610

end Max11DegreeRoutes
