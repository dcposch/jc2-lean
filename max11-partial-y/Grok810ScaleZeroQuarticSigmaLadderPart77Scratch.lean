import Grok810ScaleZeroQuarticSigmaLadderPart34Scratch

/-! Part 77 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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

section QuarticSigmaExhaust810


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
  · -- B strictly outranks G
    rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
    · -- B³ beats the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inl hFz, Or.inr hmBGlt⟩
    · -- G ties B on the mixed monomial BG
      exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hFz⟩
    · -- the mixed monomial BG strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G ties B
    exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hFz⟩
  · -- G strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
  · -- B strictly outranks F
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
    · -- B³ beats the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
        Or.inr hmBFlt, Or.inl hGz⟩
    · -- F ties B on the mixed monomial BF
      exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz, Or.inl hDz,
        Or.inl hEz, Or.inl hGz⟩
    · -- the mixed monomial BF strictly beats B³ : residual cone
      exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega), Or.inl hCz,
        Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F ties B
    exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega), Or.inl hCz,
      Or.inl hDz, Or.inl hEz, Or.inl hGz⟩
  · -- F strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz, Or.inl hDz,
      Or.inl hEz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
