import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart102Scratch

/-! Part 90 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
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
              exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBFG ⟨hA, hBne, hFne, hGne, hmBFeq, hmBGeq,
                Or.inr hBClt, Or.inr hBDlt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties B
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks B
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
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
              exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
                Or.inr hBClt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
                Or.inr hBClt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBDFG ⟨hA, hBne, hDne, hFne, hGne, hBDeq,
                hmBFeq, hmBGeq, Or.inr hBClt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks BD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
  · -- C ties B
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
              exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
                Or.inr hBDlt, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCFG ⟨hA, hBne, hCne, hFne, hGne, hBCeq,
                hmBFeq, hmBGeq, Or.inr hBDlt, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BC
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BCF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BCF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks BC
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
      · -- B strictly outranks F
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
                Or.inl hEz, Or.inr hmBFlt, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
                hmBGeq, Or.inl hEz, Or.inr hmBFlt⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
            · -- B³ beats the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
                hmBFeq, Or.inl hEz, Or.inr hmBGlt⟩
            · -- G ties B on the mixed monomial BG
              exact QuarticSigmaSupportCone810.sigmaBCDFG ⟨hA, hBne, hCne, hDne, hFne, hGne, hBCeq,
                hBDeq, hmBFeq, hmBGeq, Or.inl hEz⟩
            · -- the mixed monomial BG strictly beats B³ : residual cone
              exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BCD
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties BCD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties BCDF
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks BCDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks BCD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
                Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
                Or.inr hCDlt, Or.inl hEz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
                Or.inr hCDlt, Or.inl hEz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inr hBCgt, Or.inr hCDlt, Or.inl hEz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
    · -- D ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
                Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                Or.inr hBCgt, Or.inl hEz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                Or.inr hBCgt, Or.inl hEz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                hmCFeq, hmCGeq, Or.inr hBCgt, Or.inl hEz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties CD
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G ties CDF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- G strictly outranks CDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks CD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by omega), Or.inr hCDgt,
            Or.inl hEz, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inl hEz, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inl hEz, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inr (by omega), Or.inr hCDgt, Or.inl hEz⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDFgt, Or.inl hEz⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties B
        exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
          Or.inr hBDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks B
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BD
        exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
          Or.inr hBClt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BC
        exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
          Or.inr hBDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BC
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
          Or.inr hBElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties BCD
        exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
          hBEeq, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks BCD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
          Or.inr hCElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties C
        exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
          Or.inr hCDlt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
          Or.inr hCElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties CD
        exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
          Or.inr hBCgt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
          Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by omega), Or.inr hCDgt,
          Or.inr hDElt, Or.inl hFz, Or.inl hGz⟩
      · -- E ties D
        exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by omega),
          Or.inr hCDgt, Or.inl hFz, Or.inl hGz⟩
      · -- E strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
          Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
/-! Part 91 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_BCDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBG ⟨hA, hBne, hGne, hmBGeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties B
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties B
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBEG ⟨hA, hBne, hEne, hGne, hBEeq, hmBGeq,
              Or.inr hBClt, Or.inr hBDlt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks B
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDG ⟨hA, hBne, hDne, hGne, hBDeq, hmBGeq,
              Or.inr hBClt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BD
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties BD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
              Or.inr hBClt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBDEG ⟨hA, hBne, hDne, hEne, hGne, hBDeq, hBEeq,
              hmBGeq, Or.inr hBClt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BDE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks BD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCG ⟨hA, hBne, hCne, hGne, hBCeq, hmBGeq,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BC
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties BC
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
              Or.inr hBDlt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCEG ⟨hA, hBne, hCne, hEne, hGne, hBCeq, hBEeq,
              hmBGeq, Or.inr hBDlt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BCE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks BC
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
              Or.inr hBElt, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDG ⟨hA, hBne, hCne, hDne, hGne, hBCeq, hBDeq,
              hmBGeq, Or.inr hBElt, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BCD
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties BCD
        rcases lt_trichotomy (4 * G.natDegree) (7 * A.natDegree + 6 * B.natDegree) with hBGlt | hBGeq | hBGgt
        · -- B strictly outranks G
          rcases lt_trichotomy (G.natDegree) (A.natDegree + 2 * B.natDegree) with hmBGlt | hmBGeq | hmBGgt
          · -- B³ beats the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
              hBEeq, Or.inl hFz, Or.inr hmBGlt⟩
          · -- G ties B on the mixed monomial BG
            exact QuarticSigmaSupportCone810.sigmaBCDEG ⟨hA, hBne, hCne, hDne, hEne, hGne, hBCeq,
              hBDeq, hBEeq, hmBGeq, Or.inl hFz⟩
          · -- the mixed monomial BG strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, hmBGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties BCDE
          exact QuarticSigmaSupportCone810.mixedBG ⟨hA, hBne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks BCDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks BCD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
              Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hCElt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties C
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
              Or.inr hBCgt, Or.inr hCDlt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties CE
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks C
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inr hCEgt, Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
              Or.inr hCElt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
              Or.inr hBCgt, Or.inr hCElt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties CD
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
              Or.inr hBCgt, Or.inl hFz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
              hmCGeq, Or.inr hBCgt, Or.inl hFz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G ties CDE
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks CD
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
            Or.inr (by omega), Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inr hCEgt, Or.inr (by omega), Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by omega), Or.inr hCDgt,
            Or.inr hDElt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inr hDElt, Or.inl hFz⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inl hFz, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inr (by omega), Or.inr hCDgt, Or.inl hFz⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inl hFz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inl hFz, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hFz⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inl hFz⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_BCDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with hBClt | hBCeq | hBCgt
  · -- B strictly outranks C
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inr hBClt, Or.inr hBDlt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBF ⟨hA, hBne, hFne, hmBFeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties B
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks B
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties B
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBE ⟨hA, hBne, hEne, hBEeq, Or.inr hBClt,
              Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBEF ⟨hA, hBne, hEne, hFne, hBEeq, hmBFeq,
              Or.inr hBClt, Or.inr hBDlt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks B
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties B
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBD ⟨hA, hBne, hDne, hBDeq, Or.inr hBClt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDF ⟨hA, hBne, hDne, hFne, hBDeq, hmBFeq,
              Or.inr hBClt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BD
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties BD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDE ⟨hA, hBne, hDne, hEne, hBDeq, hBEeq,
              Or.inr hBClt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBDEF ⟨hA, hBne, hDne, hEne, hFne, hBDeq, hBEeq,
              hmBFeq, Or.inr hBClt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BDE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks BD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks B
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
  · -- C ties B
    rcases lt_trichotomy (4 * D.natDegree) (A.natDegree + 6 * B.natDegree) with hBDlt | hBDeq | hBDgt
    · -- B strictly outranks D
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBC ⟨hA, hBne, hCne, hBCeq, Or.inr hBDlt,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCF ⟨hA, hBne, hCne, hFne, hBCeq, hmBFeq,
              Or.inr hBDlt, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BC
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BC
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties BC
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCE ⟨hA, hBne, hCne, hEne, hBCeq, hBEeq,
              Or.inr hBDlt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCEF ⟨hA, hBne, hCne, hEne, hFne, hBCeq, hBEeq,
              hmBFeq, Or.inr hBDlt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BCE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BCE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks BC
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties BC
      rcases lt_trichotomy (4 * E.natDegree) (3 * A.natDegree + 6 * B.natDegree) with hBElt | hBEeq | hBEgt
      · -- B strictly outranks E
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCD ⟨hA, hBne, hCne, hDne, hBCeq, hBDeq,
              Or.inr hBElt, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDF ⟨hA, hBne, hCne, hDne, hFne, hBCeq, hBDeq,
              hmBFeq, Or.inr hBElt, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BCD
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BCD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties BCD
        rcases lt_trichotomy (4 * F.natDegree) (5 * A.natDegree + 6 * B.natDegree) with hBFlt | hBFeq | hBFgt
        · -- B strictly outranks F
          rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 4 * B.natDegree) with hmBFlt | hmBFeq | hmBFgt
          · -- B³ beats the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDE ⟨hA, hBne, hCne, hDne, hEne, hBCeq, hBDeq,
              hBEeq, Or.inr hmBFlt, Or.inl hGz⟩
          · -- F ties B on the mixed monomial BF
            exact QuarticSigmaSupportCone810.sigmaBCDEF ⟨hA, hBne, hCne, hDne, hEne, hFne, hBCeq,
              hBDeq, hBEeq, hmBFeq, Or.inl hGz⟩
          · -- the mixed monomial BF strictly beats B³ : residual cone
            exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, hmBFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties BCDE
          exact QuarticSigmaSupportCone810.mixedBF ⟨hA, hBne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks BCDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks BCD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr hBEgt, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr hBEgt,
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks BC
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr hBDgt, Or.inr (by omega),
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr hBDgt,
            Or.inr (by omega), Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr hBDgt, Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
  · -- C strictly outranks B
    rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
    · -- C strictly outranks D
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inr hBCgt, Or.inr hCDlt,
              Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hCElt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties C
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inr hBCgt,
              Or.inr hCDlt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
              Or.inr hBCgt, Or.inr hCDlt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties CE
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks C
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inr hCEgt, Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D ties C
      rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
      · -- C strictly outranks E
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inr hBCgt,
              Or.inr hCElt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
              Or.inr hBCgt, Or.inr hCElt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties CD
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E ties CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
        · -- C strictly outranks F
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
              Or.inr hBCgt, Or.inr hmCFlt, Or.inl hGz⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
              hmCFeq, Or.inr hBCgt, Or.inl hGz⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F ties CDE
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks CD
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr hCEgt,
            Or.inr (by omega), Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inr hCEgt, Or.inr (by omega), Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩
    · -- D strictly outranks C
      rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
      · -- D strictly outranks E
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inr (by omega), Or.inr hCDgt,
            Or.inr hDElt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties D
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inr hDElt, Or.inl hGz⟩
        · -- F strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E ties D
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
        · -- D strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inr (by omega),
            Or.inr hCDgt, Or.inr hDFlt, Or.inl hGz⟩
        · -- F ties DE
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inr (by omega), Or.inr hCDgt, Or.inl hGz⟩
        · -- F strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inl hGz⟩
      · -- E strictly outranks D
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
        · -- E strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inr (by omega), Or.inr (by omega),
            Or.inr hDEgt, Or.inr hEFlt, Or.inl hGz⟩
        · -- F ties E
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inr (by omega),
            Or.inr (by omega), Or.inr hDEgt, Or.inl hGz⟩
        · -- F strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inr (by omega), Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
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
