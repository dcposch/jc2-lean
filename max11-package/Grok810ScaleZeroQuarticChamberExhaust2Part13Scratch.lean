import Grok810ScaleZeroQuarticChamberExhaust2Part12Scratch

/-! Part 13 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `CDFG`. -/
theorem quarticChamberSupport810_of_live_CDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG10 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG22 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG11 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG22 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG11 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG22 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG11 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG12 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG12 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG12 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG6 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG21 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG21 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG21 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG8 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG8 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG8 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG15 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG16 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG15 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG15 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG23 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG17 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG23 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG17 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG23 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG17 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG18 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG18 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG18 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
