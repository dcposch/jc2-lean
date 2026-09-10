import Grok810ScaleZeroQuarticSigmaLadderPart73Scratch

/-! Part 74 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
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
theorem quarticSigmaSupportCone810_of_live_CDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEz : E = 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
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
            exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCG ⟨hA, hCne, hGne, hmCGeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCF ⟨hA, hCne, hFne, hmCFeq, Or.inl hBz,
              Or.inr hCDlt, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCFG ⟨hA, hCne, hFne, hGne, hmCFeq, hmCGeq,
              Or.inl hBz, Or.inr hCDlt, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties C
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks C
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties C
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
          Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties CF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
          Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks CF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks C
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
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
            exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz,
              Or.inl hEz, Or.inr hmCFlt, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDG ⟨hA, hCne, hDne, hGne, hCDeq, hmCGeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCFlt⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties C on the mixed monomial CF
          rcases lt_trichotomy (G.natDegree) (2 * C.natDegree) with hmCGlt | hmCGeq | hmCGgt
          · -- C³ beats the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDF ⟨hA, hCne, hDne, hFne, hCDeq, hmCFeq,
              Or.inl hBz, Or.inl hEz, Or.inr hmCGlt⟩
          · -- G ties C on the mixed monomial CG
            exact QuarticSigmaSupportCone810.sigmaCDFG ⟨hA, hCne, hDne, hFne, hGne, hCDeq, hmCFeq,
              hmCGeq, Or.inl hBz, Or.inl hEz⟩
          · -- the mixed monomial CG strictly beats C³ : residual cone
            exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, hmCGgt, (by omega),
              Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties CD
        rcases lt_trichotomy (A.natDegree + 2 * F.natDegree) (4 * C.natDegree) with hmCFlt | hmCFeq | hmCFgt
        · -- C³ beats the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- F ties C on the mixed monomial CF
          exact QuarticSigmaSupportCone810.mixedCG ⟨hA, hCne, hGne, (by omega), (by omega),
            Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
        · -- the mixed monomial CF strictly beats C³ : residual cone
          exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, hmCFgt, (by omega), Or.inl hBz,
            Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks CD
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties CD
      rcases lt_trichotomy (2 * G.natDegree) (2 * A.natDegree + 3 * C.natDegree) with hCGlt | hCGeq | hCGgt
      · -- C strictly outranks G
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
          Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G ties CDF
        exact QuarticSigmaSupportCone810.mixedCF ⟨hA, hCne, hFne, (by omega), (by omega),
          Or.inl hBz, Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
      · -- G strictly outranks CDF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks CD
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by omega), Or.inr (by omega), Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with hDFlt | hDFeq | hDFgt
    · -- D strictly outranks F
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inl hEz,
          Or.inr hDFlt, Or.inr hDGlt⟩
      · -- G ties D
        exact QuarticSigmaSupportCone810.sigmaDG ⟨hA, hDne, hGne, hDGeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDFlt⟩
      · -- G strictly outranks D
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
    · -- F ties D
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with hDGlt | hDGeq | hDGgt
      · -- D strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaDF ⟨hA, hDne, hFne, hDFeq, Or.inl hBz, Or.inr hCDgt,
          Or.inl hEz, Or.inr hDGlt⟩
      · -- G ties DF
        exact QuarticSigmaSupportCone810.sigmaDFG ⟨hA, hDne, hFne, hGne, hDFeq, hDGeq, Or.inl hBz,
          Or.inr hCDgt, Or.inl hEz⟩
      · -- G strictly outranks DF
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr hDGgt, Or.inl hEz, Or.inr (by omega)⟩
    · -- F strictly outranks D
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with hFGlt | hFGeq | hFGgt
      · -- F strictly outranks G
        exact QuarticSigmaSupportCone810.sigmaF ⟨hA, hFne, Or.inl hBz, Or.inr (by omega),
          Or.inr hDFgt, Or.inl hEz, Or.inr hFGlt⟩
      · -- G ties F
        exact QuarticSigmaSupportCone810.sigmaFG ⟨hA, hFne, hGne, hFGeq, Or.inl hBz,
          Or.inr (by omega), Or.inr hDFgt, Or.inl hEz⟩
      · -- G strictly outranks F
        exact QuarticSigmaSupportCone810.sigmaG ⟨hA, hGne, Or.inl hBz, Or.inr (by omega),
          Or.inr (by omega), Or.inl hEz, Or.inr hFGgt⟩


set_option maxHeartbeats 64000000 in
theorem quarticSigmaSupportCone810_of_live_CDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    QuarticSigmaSupportCone810 A B C D E F G := by
  have ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hA
  rcases lt_trichotomy (A.natDegree + 2 * D.natDegree) (3 * C.natDegree) with hCDlt | hCDeq | hCDgt
  · -- C strictly outranks D
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaC ⟨hA, hCne, Or.inl hBz, Or.inr hCDlt, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties C
      exact QuarticSigmaSupportCone810.sigmaCE ⟨hA, hCne, hEne, hCEeq, Or.inl hBz, Or.inr hCDlt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks C
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
  · -- D ties C
    rcases lt_trichotomy (2 * E.natDegree) (3 * C.natDegree) with hCElt | hCEeq | hCEgt
    · -- C strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaCD ⟨hA, hCne, hDne, hCDeq, Or.inl hBz, Or.inr hCElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties CD
      exact QuarticSigmaSupportCone810.sigmaCDE ⟨hA, hCne, hDne, hEne, hCDeq, hCEeq, Or.inl hBz,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks CD
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr hCEgt,
        Or.inr (by omega), Or.inl hFz, Or.inl hGz⟩
  · -- D strictly outranks C
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with hDElt | hDEeq | hDEgt
    · -- D strictly outranks E
      exact QuarticSigmaSupportCone810.sigmaD ⟨hA, hDne, Or.inl hBz, Or.inr hCDgt, Or.inr hDElt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E ties D
      exact QuarticSigmaSupportCone810.sigmaDE ⟨hA, hDne, hEne, hDEeq, Or.inl hBz, Or.inr hCDgt,
        Or.inl hFz, Or.inl hGz⟩
    · -- E strictly outranks D
      exact QuarticSigmaSupportCone810.sigmaE ⟨hA, hEne, Or.inl hBz, Or.inr (by omega),
        Or.inr hDEgt, Or.inl hFz, Or.inl hGz⟩


end QuarticSigmaExhaust810
end Max11DegreeRoutes
end
