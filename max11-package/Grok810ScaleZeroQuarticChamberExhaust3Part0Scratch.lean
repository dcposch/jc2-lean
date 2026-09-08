import Grok810ScaleZeroQuarticChamberDefs4Scratch

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

end QuarticChamberExhaust810

end Max11DegreeRoutes
