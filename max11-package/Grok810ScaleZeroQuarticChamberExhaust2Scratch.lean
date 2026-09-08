import Grok810ScaleZeroQuarticChamberExhaust1Scratch

/-! # Cost-argmin chamber exhaust (2/4), `(8,10)` scale zero

The 15 live-letter sets with |S| ∈ {4}.  Each theorem runs the case tree
of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,
`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,
`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`
against each other.  Branches no chamber matches are ℚ-infeasible
(exact Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.
Untracked working note.
-/

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

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDF`. -/
theorem quarticChamberSupport810_of_live_BCDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF23 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

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

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEG`. -/
theorem quarticChamberSupport810_of_live_BCEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG22 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG10 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG11 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG10 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG10 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG12 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG12 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG12 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG13 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG13 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG13 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG23 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG6 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG7 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG6 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG6 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG8 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG8 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG8 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG9 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG9 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG9 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG24 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG17 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG18 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG17 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG17 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG19 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG19 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG19 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG20 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG20 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG20 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

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

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEF`. -/
theorem quarticChamberSupport810_of_live_BDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEG`. -/
theorem quarticChamberSupport810_of_live_BDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG14 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG4 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG18 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG8 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG18 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG8 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG18 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG8 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG17 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG6 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG7 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG6 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG6 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG15 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG15 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG15 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG20 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG9 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG10 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG9 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG9 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG21 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG11 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG21 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG11 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG21 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG11 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDFG`. -/
theorem quarticChamberSupport810_of_live_BDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG10 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG22 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG11 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG22 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG11 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG22 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG11 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG12 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG12 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG12 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG6 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG21 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG21 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG21 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG8 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG8 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG8 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG15 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG16 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG15 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG15 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG23 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG17 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG23 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG17 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG23 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG17 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG18 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · -- D.natDegree = A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG18 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- D.natDegree > A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG18 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BEFG`. -/
theorem quarticChamberSupport810_of_live_BEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG10 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG22 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG11 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG22 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG11 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG22 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG11 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG12 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG12 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG12 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG6 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG21 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG21 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG21 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG8 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG8 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + B.natDegree < F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree = F.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG8 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG15 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG16 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG15 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG15 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG23 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG17 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG23 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG17 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG23 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG17 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG18 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG18 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG18 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEF`. -/
theorem quarticChamberSupport810_of_live_CDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

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

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CEFG`. -/
theorem quarticChamberSupport810_of_live_CEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG10 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG22 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG11 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG22 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG11 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG22 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG11 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG12 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG12 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG12 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG6 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG21 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG21 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG21 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG8 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG8 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG8 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG15 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG16 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG15 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG15 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG23 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG17 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG23 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG17 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG23 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG17 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG18 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · -- E.natDegree = A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG18 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
      · -- E.natDegree > A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * A.natDegree + C.natDegree < G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree = G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG18 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact (by omega : False).elim
          · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DEFG`. -/
theorem quarticChamberSupport810_of_live_DEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG6 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG5 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG7 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG2 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG1 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG3 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG10 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG9 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG11 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)


end QuarticChamberExhaust810

end Max11DegreeRoutes
