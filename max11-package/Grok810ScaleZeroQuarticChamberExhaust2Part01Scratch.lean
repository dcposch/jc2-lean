import Grok810ScaleZeroQuarticChamberExhaust1Scratch

/-! Part 1 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDE`. -/
theorem quarticChamberSupport810_of_live_BCDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE13 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE10 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
