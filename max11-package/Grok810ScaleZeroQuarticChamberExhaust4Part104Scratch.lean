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
/-- Cost-argmin subtree on the three comparison branches `122`. -/
private theorem chamberExhaustBCDEFGPath122
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1c : (A.natDegree + 2 * D.natDegree) < (2 * E.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
/-- Cost-argmin subtree on the three comparison branches `200`. -/
private theorem chamberExhaustBCDEFGPath200
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
/-- Cost-argmin subtree on the three comparison branches `201`. -/
private theorem chamberExhaustBCDEFGPath201
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
/-- Cost-argmin subtree on the three comparison branches `202`. -/
private theorem chamberExhaustBCDEFGPath202
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
/-- Cost-argmin subtree on the three comparison branches `210`. -/
private theorem chamberExhaustBCDEFGPath210
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
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
/-- Cost-argmin subtree on the three comparison branches `211`. -/
private theorem chamberExhaustBCDEFGPath211
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
