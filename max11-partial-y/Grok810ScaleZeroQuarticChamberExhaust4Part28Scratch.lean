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
/-- Cost-argmin subtree on the three comparison branches `222`. -/
private theorem chamberExhaustBCDEFGPath222
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1c : (A.natDegree + 2 * D.natDegree) < (2 * E.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
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

end QuarticChamberExhaust810

end Max11DegreeRoutes
