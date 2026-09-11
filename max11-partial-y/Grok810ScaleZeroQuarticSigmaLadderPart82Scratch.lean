import Grok810ScaleZeroQuarticSigmaLadderPart34Scratch

/-! Part 82 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
              Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
              Or.inl hCz, Or.inr hBDlt, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties B
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties BF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks BF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks B
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
  · -- D ties B
    rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
    · -- B strictly outranks F
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
              Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBFlt⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties B on the mixed monomial BF
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
              Or.inl hCz, Or.inl hEz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq, hmBFeq,
              hmBGeq, Or.inl hCz, Or.inl hEz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
        · -- B³ beats the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties B on the mixed monomial BF
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial BF strictly beats B³ : residual cone
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties BD
      rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
      · -- B strictly outranks G
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties BDF
        exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks BDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks BD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
          Or.inl hCz, Or.inr (by omega), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt, Or.inl hCz,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
          Or.inr hBDgt, Or.inl hCz, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
          Or.inl hCz, Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
          Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties B
      exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz, Or.inr hBDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks B
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz, Or.inr hBElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties BD
      exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks BD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
        Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt, Or.inl hCz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inl hCz,
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
