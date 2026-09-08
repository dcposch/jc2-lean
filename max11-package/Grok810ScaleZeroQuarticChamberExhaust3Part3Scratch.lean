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

end QuarticChamberExhaust810

end Max11DegreeRoutes
