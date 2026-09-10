import Grok810ScaleZeroQuarticChamberExhaust2Part02Scratch

/-! Part 3 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDG`. -/
theorem quarticChamberSupport810_of_live_BCDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG22 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG10 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG11 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG10 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG10 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG12 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG12 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG12 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG13 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG13 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG13 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG23 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG6 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG7 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG6 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG6 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG8 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG8 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG8 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG9 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG9 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG9 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG24 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG17 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG18 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG17 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG17 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG19 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG19 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG19 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG20 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG20 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG20 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
