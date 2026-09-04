import Grok810ScaleZeroQuarticChamberExhaust2Scratch

/-! # Cost-argmin chamber exhaust (3/4), `(8,10)` scale zero

The 6 live-letter sets with |S| ∈ {5}.  Each theorem runs the case tree
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDEF`. -/
theorem quarticChamberSupport810_of_live_BCDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF40 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF45 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF19 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF20 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF19 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF19 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF22 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF23 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF22 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF22 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF41 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF46 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF9 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF10 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF9 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF9 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF12 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF13 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF12 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF12 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF42 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF30 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF34 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF34 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF34 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF47 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF33 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF31 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF31 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF31 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF36 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF37 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF37 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF37 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEF27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGz, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDEG`. -/
theorem quarticChamberSupport810_of_live_BCDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG40 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG16 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG17 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG16 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG16 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG21 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG21 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG21 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG45 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG19 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG20 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG19 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG19 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG18 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG18 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG18 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG50 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG22 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG23 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG22 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG22 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG24 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG24 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG24 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG41 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG46 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG10 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG51 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG13 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG42 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG29 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG30 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG29 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG29 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG34 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG34 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG34 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG47 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG32 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG33 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG32 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG32 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG31 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG31 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG31 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG52 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG35 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG36 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG35 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG35 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG37 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG37 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG37 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDFG`. -/
theorem quarticChamberSupport810_of_live_BCDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG23 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG34 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG35 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG34 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG34 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG36 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG36 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG36 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG37 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG37 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG37 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG30 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG31 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG30 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG30 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG32 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG32 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG32 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG33 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG33 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG33 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG47 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG48 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG47 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG47 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG49 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG49 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG49 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG50 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG50 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG50 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG43 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG44 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG43 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG43 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG45 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG45 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG45 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG46 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG46 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG46 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG53 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG54 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG53 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG53 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG55 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG55 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG55 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG56 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG56 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG56 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEFG`. -/
theorem quarticChamberSupport810_of_live_BCEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG23 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG34 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG35 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG34 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG34 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG36 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG36 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG36 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG37 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG37 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG37 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG30 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG31 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG30 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG30 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG32 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG32 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG32 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG33 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG33 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG33 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG47 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG48 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG47 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG47 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG49 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG49 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG49 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG50 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG50 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG50 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG43 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG44 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG43 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG43 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG45 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG45 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG45 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG46 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG46 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG46 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG53 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG54 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG53 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG53 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG55 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG55 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG55 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG56 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG56 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG56 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEFG`. -/
theorem quarticChamberSupport810_of_live_BDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG45 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG45 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG45 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG44 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG44 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG44 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG27 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG28 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG27 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG27 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG46 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG32 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG46 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG32 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG46 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG32 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG40 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG40 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG40 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG39 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG39 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG39 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG30 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG31 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG30 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG30 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG41 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG29 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG41 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG29 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG41 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG29 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- D.natDegree = A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- D.natDegree > A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG50 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG23 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG50 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG23 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG50 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG23 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG49 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG49 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG49 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + B.natDegree < F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree = F.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG33 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG34 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG33 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG33 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG51 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG35 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG51 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG35 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG51 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG35 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEFG`. -/
theorem quarticChamberSupport810_of_live_CDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG45 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG45 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG45 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG44 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG44 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG44 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG27 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG28 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG27 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG27 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG46 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG32 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG46 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG32 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG46 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG32 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG40 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG40 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG40 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG39 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG39 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG39 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG30 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG31 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG30 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG30 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG41 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG29 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG41 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG29 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG41 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG29 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG50 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG23 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG50 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG23 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG50 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG23 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG49 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG49 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG49 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG33 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG34 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG33 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG33 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG51 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG35 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG51 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG35 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG51 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG35 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · -- E.natDegree = A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
        · -- E.natDegree > A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * A.natDegree + C.natDegree < G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree = G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact (by omega : False).elim
            · exact (by omega : False).elim


end QuarticChamberExhaust810

end Max11DegreeRoutes
