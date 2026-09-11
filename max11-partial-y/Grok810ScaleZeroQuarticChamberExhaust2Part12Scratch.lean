import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! Part 12 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEG`. -/
theorem quarticChamberSupport810_of_live_CDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG14 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG4 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG18 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG8 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG18 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG8 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG18 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG8 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG17 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG6 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG7 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG6 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG6 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG15 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG15 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG15 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG20 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG9 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG10 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG9 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG9 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG21 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG11 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG21 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG11 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG21 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG11 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
