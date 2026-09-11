import Grok810ScaleZeroQuarticSigmaLadderPart34Scratch

/-! Part 84 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
  · -- B strictly outranks D
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inr hBDlt,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties B
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inl hCz,
                Or.inr hBDlt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
                Or.inl hCz, Or.inr hBDlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBEFG ⟨hA, hBne, hEne, hFne, hGne, hBEeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBDlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties BE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks BE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks B
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by omega), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by omega), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by omega), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by omega)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
  · -- D ties B
    rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
    · -- B strictly outranks E
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inl hCz,
                Or.inr hBElt, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                Or.inl hCz, Or.inr hBElt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                hmBFeq, hmBGeq, Or.inl hCz, Or.inr hBElt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks BD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties BD
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
                Or.inl hCz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
                hmBGeq, Or.inl hCz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
                hmBFeq, Or.inl hCz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDEFG ⟨hA, hBne, hDne, hEne, hFne, hGne, hBDeq,
                hBEeq, hmBFeq, hmBGeq, Or.inl hCz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BDE
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties BDE
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties BDEF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks BDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks BDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks BD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inl hCz,
            Or.inr (by omega), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by omega), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inl hCz, Or.inr (by omega), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr hBEgt, Or.inl hCz, Or.inr (by omega)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
  · -- D strictly outranks B
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inl hCz,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inl hCz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inl hCz, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inr hBDgt, Or.inl hCz⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDFgt, Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr hDFgt, Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inl hCz,
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inl hCz, Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inr (by omega), Or.inl hCz, Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inl hCz, Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inl hCz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BC
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inl hDz, Or.inl hEz,
      Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
