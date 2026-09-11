import Grok810ScaleZeroQuarticChamberDefs4Scratch

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
/-- Cost-argmin subtree on the three comparison branches `000`. -/
private theorem chamberExhaustBCDEFGPath000
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0a : (2 * C.natDegree) < (A.natDegree + 2 * B.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
