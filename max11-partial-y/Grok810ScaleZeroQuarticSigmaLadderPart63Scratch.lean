import Grok810ScaleZeroQuarticSigmaLadderPart34Scratch

/-! Part 63 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_EG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
  · -- E strictly outranks G
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inl hFz, Or.inr hEGlt⟩
  · -- G ties E
    exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hFz⟩
  · -- G strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_EF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
  · -- E strictly outranks F
    exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFlt, Or.inl hGz⟩
  · -- F ties E
    exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inl hCz,
      Or.inl hDz, Or.inl hGz⟩
  · -- F strictly outranks E
    exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inl hCz, Or.inl hDz,
      Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
