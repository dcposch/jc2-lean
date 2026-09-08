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
