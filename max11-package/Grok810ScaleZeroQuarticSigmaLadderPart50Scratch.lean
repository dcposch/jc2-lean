import Grok810ScaleZeroQuarticSigmaLadderPart48Scratch

/-! Part 50 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticKappaLadder810


/-- κ kills `zeta` when `2s > 7 a`, expanded per letter. -/
def QuarticKappaLoadTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B = 0 ∧
    (C = 0 ∨ 4 * C.natDegree < A.natDegree) ∧
    (D = 0 ∨ 4 * D.natDegree < 3 * A.natDegree) ∧
    (E = 0 ∨ 4 * E.natDegree < 5 * A.natDegree) ∧
    (F = 0 ∨ 4 * F.natDegree < 7 * A.natDegree) ∧
    (G = 0 ∨ 4 * G.natDegree < 9 * A.natDegree)


theorem quarticKappaLoadTopL810_bounds
    {A B C D E F G : k[X]}
    (h : QuarticKappaLoadTopL810 A B C D E F G) :
    0 < A.natDegree ∧
      2 * B.natDegree < 3 * A.natDegree ∧
      C.natDegree < 2 * A.natDegree ∧
      2 * D.natDegree < 5 * A.natDegree ∧
      E.natDegree < 3 * A.natDegree ∧
      2 * F.natDegree < 7 * A.natDegree ∧
      G.natDegree < 4 * A.natDegree ∧
      4 * B.natDegree < 5 * A.natDegree ∧
      4 * C.natDegree < 7 * A.natDegree ∧
      4 * D.natDegree < 9 * A.natDegree ∧
      4 * E.natDegree < 11 * A.natDegree ∧
      4 * F.natDegree < 13 * A.natDegree ∧
      4 * G.natDegree < 15 * A.natDegree := by
  rcases h with ⟨hA, hB, hC, hD, hE, hF, hG⟩
  rcases hA with ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  refine ⟨hApos, by omega, by omega, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hB with h0 | hlt
    · have : B.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hC with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hD with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hE with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hF with h0 | hlt
    · have : F.natDegree = 0 := by simp [h0]
      omega
    · exact hlt
  · rcases hG with h0 | hlt
    · have : G.natDegree = 0 := by simp [h0]
      omega
    · exact hlt


end QuarticKappaLadder810
end Max11DegreeRoutes
end
