import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! Part 6 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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

section QuarticChamberExhaust810


set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCFG`. -/
theorem quarticChamberSupport810_of_live_BCFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG13 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG2 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG3 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG9 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG4 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG5 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG19 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG14 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG15 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG12 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG10 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG11 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG8 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG6 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG7 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG18 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG16 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG17 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG26 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG21 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG22 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG25 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG23 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG24 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG29 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG27 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG28 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
