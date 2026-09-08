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

section CubicLoadMultiBandSpecialize610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicLoadSigmaConeBCE610_specialize_delta
    {delta : k} {A B C D E : k[X]}
    (hcone : CubicLoadSigmaConeBCE610 A B C D E)
    (hband : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree)) :
    (delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree) := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hEne, heq1, heq2, hDcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree ∨ D.natDegree = 0 := by
    rcases hDcmp with h0 | hlt
    · exact Or.inr (by simp [h0])
    · exact Or.inl (Nat.succ_le_of_lt hlt)
  rcases hband with h | h | h | h | h
  · exact Or.inl h
  · -- B-summand of the four-way OR
    exact Or.inr h
  · -- C-summand of the four-way OR
    omega
  · -- D-summand of the four-way OR
    rcases hsD with hsD | hD0
    · omega
    · omega
  · -- E-summand of the four-way OR
    omega

end CubicLoadMultiBandSpecialize610

end Max11DegreeRoutes
