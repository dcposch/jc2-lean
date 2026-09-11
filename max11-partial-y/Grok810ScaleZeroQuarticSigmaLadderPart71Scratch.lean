import Grok810ScaleZeroQuarticSigmaLadderPart34Scratch

/-! Part 71 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega), Or.inl hBz,
          Or.inl hDz, Or.inr (by omega), Or.inl hFz⟩
    · -- G ties C
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega), Or.inl hBz,
        Or.inl hDz, Or.inr (by omega), Or.inl hFz⟩
    · -- G strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr (by omega), Or.inl hFz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
    · -- C strictly outranks G
      rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
      · -- C³ beats the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inl hFz, Or.inr hmCGlt⟩
      · -- G ties C on the mixed monomial CG
        exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq, Or.inl hBz,
          Or.inl hDz, Or.inl hFz⟩
      · -- the mixed monomial CG strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega), Or.inl hBz,
          Or.inl hDz, Or.inr (by omega), Or.inl hFz⟩
    · -- G ties CE
      exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega), Or.inl hBz,
        Or.inl hDz, Or.inr (by omega), Or.inl hFz⟩
    · -- G strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr (by omega), Or.inl hFz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
    · -- E strictly outranks G
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inl hFz, Or.inr hEGlt⟩
    · -- G ties E
      exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hFz⟩
    · -- G strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
  · -- C strictly outranks E
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inl hDz, Or.inr hCElt,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz, Or.inl hDz,
          Or.inr hCElt, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
          Or.inl hDz, Or.inr (by omega), Or.inl hGz⟩
    · -- F ties C
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega), Or.inl hBz,
        Or.inl hDz, Or.inr (by omega), Or.inl hGz⟩
    · -- F strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr (by omega), Or.inl hGz⟩
  · -- E ties C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
    · -- C strictly outranks F
      rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
      · -- C³ beats the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inl hDz,
          Or.inr hmCFlt, Or.inl hGz⟩
      · -- F ties C on the mixed monomial CF
        exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq, Or.inl hBz,
          Or.inl hDz, Or.inl hGz⟩
      · -- the mixed monomial CF strictly beats C³ : residual cone
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
          Or.inl hDz, Or.inr (by omega), Or.inl hGz⟩
    · -- F ties CE
      exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega), Or.inl hBz,
        Or.inl hDz, Or.inr (by omega), Or.inl hGz⟩
    · -- F strictly outranks CE
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr (by omega), Or.inl hGz⟩
  · -- E strictly outranks C
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
    · -- E strictly outranks F
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt, Or.inl hDz,
        Or.inr hEFlt, Or.inl hGz⟩
    · -- F ties E
      exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz, Or.inr hCEgt,
        Or.inl hDz, Or.inl hGz⟩
    · -- F strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega), Or.inl hDz,
        Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
