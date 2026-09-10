import Grok810ScaleZeroQuarticChamberExhaust2Part03Scratch

/-! Part 4 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEF`. -/
theorem quarticChamberSupport810_of_live_BCEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF23 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
