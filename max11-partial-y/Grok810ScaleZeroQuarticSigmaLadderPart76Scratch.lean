import Grok810ScaleZeroQuarticSigmaLadderPart75Scratch

/-! Part 76 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties C
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks C
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties C
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks C
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz,
                Or.inr hCDlt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEG ⟨hA, hCne, hEne, hGne, hCEeq, hmCGeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEF ⟨hA, hCne, hEne, hFne, hCEeq, hmCFeq,
                Or.inl hBz, Or.inr hCDlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCEFG ⟨hA, hCne, hEne, hFne, hGne, hCEeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCDlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties CE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks CE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks C
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by omega), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by omega), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by omega), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by omega)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
                Or.inr hCElt, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
                Or.inl hBz, Or.inr hCElt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq,
                hmCFeq, hmCGeq, Or.inl hBz, Or.inr hCElt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CD
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CD
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties CD
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CDF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CDF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks CD
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 3 * C.natDegree) with hCFlt | hCFeq | hCFgt
      · -- C strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq,
                Or.inl hBz, Or.inr hmCFlt, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEG ⟨hA, hCne, hDne, hEne, hGne, hCDeq, hCEeq,
                hmCGeq, Or.inl hBz, Or.inr hmCFlt⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
            · -- C³ beats the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEF ⟨hA, hCne, hDne, hEne, hFne, hCDeq, hCEeq,
                hmCFeq, Or.inl hBz, Or.inr hmCGlt⟩
            · -- G ties C on the mixed monomial CG
              exact QuarticSigmaSupportCone810.sigmaCDEFG ⟨hA, hCne, hDne, hEne, hFne, hGne, hCDeq,
                hCEeq, hmCFeq, hmCGeq, Or.inl hBz⟩
            · -- the mixed monomial CG strictly beats C³ : residual cone
              exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
                Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CDE
          rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
          · -- C³ beats the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- F ties C on the mixed monomial CF
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
          · -- the mixed monomial CF strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CDE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties CDE
        rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
        · -- C strictly outranks G
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G ties CDEF
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks CDEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks CDE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks CD
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
            Or.inr (by omega), Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by omega), Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr hCEgt, Or.inr (by omega), Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr hCEgt, Or.inr (by omega)⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt,
            Or.inr hDElt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties D
          exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDFlt⟩
        · -- G strictly outranks D
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties D
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDElt, Or.inr hDGlt⟩
        · -- G ties DF
          exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDElt⟩
        · -- G strictly outranks DF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks D
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr hDFgt, Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E ties D
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
      · -- D strictly outranks F
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz,
            Or.inr hCDgt, Or.inr hDFlt, Or.inr hDGlt⟩
        · -- G ties DE
          exact QuarticSigmaSupportCone810.sigmaDEG ⟨hA, hDne, hEne, hGne, hDEeq, hDGeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDFlt⟩
        · -- G strictly outranks DE
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F ties DE
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
        · -- D strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaDEF ⟨hA, hDne, hEne, hFne, hDEeq, hDFeq,
            Or.inl hBz, Or.inr hCDgt, Or.inr hDGlt⟩
        · -- G ties DEF
          exact QuarticSigmaSupportCone810.sigmaDEFG ⟨hA, hDne, hEne, hFne, hGne, hDEeq, hDFeq,
            hDGeq, Or.inl hBz, Or.inr hCDgt⟩
        · -- G strictly outranks DEF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDGgt, Or.inr (by omega), Or.inr (by omega)⟩
      · -- F strictly outranks DE
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDFgt, Or.inr (by omega), Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr hDFgt, Or.inr (by omega)⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩
    · -- E strictly outranks D
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with hEFlt | hEFeq | hEFgt
      · -- E strictly outranks F
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by omega),
            Or.inr hDEgt, Or.inr hEFlt, Or.inr hEGlt⟩
        · -- G ties E
          exact QuarticSigmaSupportCone810.sigmaEG ⟨hA, hEne, hGne, hEGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr hDEgt, Or.inr hEFlt⟩
        · -- G strictly outranks E
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F ties E
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with hEGlt | hEGeq | hEGgt
        · -- E strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaEF ⟨hA, hEne, hFne, hEFeq, Or.inl hBz,
            Or.inr (by omega), Or.inr hDEgt, Or.inr hEGlt⟩
        · -- G ties EF
          exact QuarticSigmaSupportCone810.sigmaEFG ⟨hA, hEne, hFne, hGne, hEFeq, hEGeq,
            Or.inl hBz, Or.inr (by omega), Or.inr hDEgt⟩
        · -- G strictly outranks EF
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEGgt, Or.inr (by omega)⟩
      · -- F strictly outranks E
        rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
        · -- F strictly outranks G
          exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr hEFgt, Or.inr hFGlt⟩
        · -- G ties F
          exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
            Or.inr (by omega), Or.inr (by omega), Or.inr hEFgt⟩
        · -- G strictly outranks F
          exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
            Or.inr (by omega), Or.inr (by omega), Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_B
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  exact QuarticSigmaSupportCone810.sigmaB ⟨hA, hBne, Or.inl hCz, Or.inl hDz, Or.inl hEz,
    Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
