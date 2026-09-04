import Grok810ScaleZeroQuarticChamberExhaust3Scratch

/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDEFG`. -/
theorem quarticChamberSupport810_of_live_BCDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG112 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG40 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG41 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG40 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG40 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG45 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG45 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG45 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG112 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG19 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG18 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG23 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG23 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG23 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG112 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG64 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG65 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG64 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG64 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG69 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG69 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG69 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG119 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG44 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG43 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG42 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG42 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG42 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG119 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG22 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG21 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG20 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG20 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG20 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG119 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG67 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG68 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG67 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG67 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG66 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG66 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG66 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG46 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG47 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG46 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG46 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · -- G.natDegree < A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG70 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG71 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG70 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG70 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree = A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG72 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG72 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG72 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree > A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG30 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG31 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG30 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG30 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG9 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG13 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG13 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG13 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG55 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG59 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG59 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG59 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG33 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG34 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG33 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG33 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG12 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG10 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG10 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- B.natDegree + F.natDegree < 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree = 2 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG10 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- B.natDegree + F.natDegree > 2 * D.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG57 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG58 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG57 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG57 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG56 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG56 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG56 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
          · -- D.natDegree < A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- D.natDegree = A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- D.natDegree > A.natDegree + B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG36 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG37 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG36 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG36 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + B.natDegree < F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree = F.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + B.natDegree > F.natDegree
              rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · -- G.natDegree < A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG60 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG61 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG60 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG60 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree = A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG62 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG62 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG62 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree > A.natDegree + E.natDegree
          rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
            rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
            · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
              rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG89 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG90 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG89 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG89 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG94 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG94 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG94 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG79 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG80 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG79 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG79 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG84 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG84 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG84 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG101 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG102 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG101 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG101 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG106 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG106 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG106 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG121 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG92 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG93 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG92 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG92 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG91 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG91 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG91 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
        · -- F.natDegree < A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG121 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG82 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG83 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG82 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG82 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree = A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG81 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG81 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG81 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- F.natDegree > A.natDegree + D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG121 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG104 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG105 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG104 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG104 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG103 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG103 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG103 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG128 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG95 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG96 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG95 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG95 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG97 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG97 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG97 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG128 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG85 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG86 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG85 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG85 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG87 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG87 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG87 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
              rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
      · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
        rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · -- G.natDegree < A.natDegree + E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG128 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG107 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG108 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG107 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG107 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree = A.natDegree + E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG109 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG109 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · -- C.natDegree + G.natDegree < 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree = 2 * E.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG109 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- C.natDegree + G.natDegree > 2 * E.natDegree
              rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
        · -- G.natDegree > A.natDegree + E.natDegree
          rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht4a | ht4b | ht4c
          · -- E.natDegree < A.natDegree + C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
          · -- E.natDegree = A.natDegree + C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
          · -- E.natDegree > A.natDegree + C.natDegree
            rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · -- 2 * A.natDegree + C.natDegree < G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree = G.natDegree
              rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim
            · -- 2 * A.natDegree + C.natDegree > G.natDegree
              rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht6a | ht6b | ht6c
              · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
              · exact (by omega : False).elim
              · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Every point of cone `A` with a live letter sits in exactly one
cost-argmin chamber. -/
theorem quarticChamberSupport810_of
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    QuarticChamberSupport810 A B C D E F G := by
  by_cases hBz : B = 0
  · -- B vanishes
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact (quarticSigmaSupportCone810_of_allZero A B C D E F G hA l beta gamma delta epsilon zeta eta theta hjdiv hder hBz hCz hDz hEz hFz hGz).elim
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_G A B C D E F G hA hBz hCz hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_F A B C D E F G hA hBz hCz hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_FG A B C D E F G hA hBz hCz hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_E A B C D E F G hA hBz hCz hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_EG A B C D E F G hA hBz hCz hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_EF A B C D E F G hA hBz hCz hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_EFG A B C D E F G hA hBz hCz hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_D A B C D E F G hA hBz hCz hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DG A B C D E F G hA hBz hCz hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DF A B C D E F G hA hBz hCz hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DFG A B C D E F G hA hBz hCz hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DE A B C D E F G hA hBz hCz hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DEG A B C D E F G hA hBz hCz hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_DEF A B C D E F G hA hBz hCz hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_DEFG A B C D E F G hA hBz hCz hDne hEne hFne hGne
    · -- C lives
      have hCne : C ≠ 0 := hCz
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_C A B C D E F G hA hBz hCne hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CG A B C D E F G hA hBz hCne hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CF A B C D E F G hA hBz hCne hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CFG A B C D E F G hA hBz hCne hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CE A B C D E F G hA hBz hCne hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CEG A B C D E F G hA hBz hCne hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CEF A B C D E F G hA hBz hCne hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CEFG A B C D E F G hA hBz hCne hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CD A B C D E F G hA hBz hCne hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDG A B C D E F G hA hBz hCne hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDF A B C D E F G hA hBz hCne hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDFG A B C D E F G hA hBz hCne hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDE A B C D E F G hA hBz hCne hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDEG A B C D E F G hA hBz hCne hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_CDEF A B C D E F G hA hBz hCne hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_CDEFG A B C D E F G hA hBz hCne hDne hEne hFne hGne
  · -- B lives
    have hBne : B ≠ 0 := hBz
    by_cases hCz : C = 0
    · -- C vanishes
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_B A B C D E F G hA hBne hCz hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BG A B C D E F G hA hBne hCz hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BF A B C D E F G hA hBne hCz hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BFG A B C D E F G hA hBne hCz hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BE A B C D E F G hA hBne hCz hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BEG A B C D E F G hA hBne hCz hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BEF A B C D E F G hA hBne hCz hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BEFG A B C D E F G hA hBne hCz hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BD A B C D E F G hA hBne hCz hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDG A B C D E F G hA hBne hCz hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDF A B C D E F G hA hBne hCz hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDFG A B C D E F G hA hBne hCz hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDE A B C D E F G hA hBne hCz hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDEG A B C D E F G hA hBne hCz hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BDEF A B C D E F G hA hBne hCz hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BDEFG A B C D E F G hA hBne hCz hDne hEne hFne hGne
    · -- C lives
      have hCne : C ≠ 0 := hCz
      by_cases hDz : D = 0
      · -- D vanishes
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BC A B C D E F G hA hBne hCne hDz hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCG A B C D E F G hA hBne hCne hDz hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCF A B C D E F G hA hBne hCne hDz hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCFG A B C D E F G hA hBne hCne hDz hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCE A B C D E F G hA hBne hCne hDz hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCEG A B C D E F G hA hBne hCne hDz hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCEF A B C D E F G hA hBne hCne hDz hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCEFG A B C D E F G hA hBne hCne hDz hEne hFne hGne
      · -- D lives
        have hDne : D ≠ 0 := hDz
        by_cases hEz : E = 0
        · -- E vanishes
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCD A B C D E F G hA hBne hCne hDne hEz hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDG A B C D E F G hA hBne hCne hDne hEz hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDF A B C D E F G hA hBne hCne hDne hEz hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDFG A B C D E F G hA hBne hCne hDne hEz hFne hGne
        · -- E lives
          have hEne : E ≠ 0 := hEz
          by_cases hFz : F = 0
          · -- F vanishes
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDE A B C D E F G hA hBne hCne hDne hEne hFz hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDEG A B C D E F G hA hBne hCne hDne hEne hFz hGne
          · -- F lives
            have hFne : F ≠ 0 := hFz
            by_cases hGz : G = 0
            · -- G vanishes
              exact quarticChamberSupport810_of_live_BCDEF A B C D E F G hA hBne hCne hDne hEne hFne hGz
            · -- G lives
              have hGne : G ≠ 0 := hGz
              exact quarticChamberSupport810_of_live_BCDEFG A B C D E F G hA hBne hCne hDne hEne hFne hGne


end QuarticChamberExhaust810

#print axioms quarticChamberSupport810_of

end Max11DegreeRoutes
