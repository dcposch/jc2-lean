import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # Cost-argmin chamber exhaust (1/4), `(8,10)` scale zero

The 41 live-letter sets with |S| ∈ {1, 2, 3}.  Each theorem runs the case tree
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
/-- Exhaust of the cost-argmin taxonomy on the live set `B`. -/
theorem quarticChamberSupport810_of_live_B
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cB0 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGz⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `C`. -/
theorem quarticChamberSupport810_of_live_C
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cC0 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGz⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `D`. -/
theorem quarticChamberSupport810_of_live_D
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cD0 ⟨hA, hBz, hCz, hDne, hEz, hFz, hGz⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `E`. -/
theorem quarticChamberSupport810_of_live_E
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cE0 ⟨hA, hBz, hCz, hDz, hEne, hFz, hGz⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `F`. -/
theorem quarticChamberSupport810_of_live_F
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cF0 ⟨hA, hBz, hCz, hDz, hEz, hFne, hGz⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `G`. -/
theorem quarticChamberSupport810_of_live_G
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  exact QuarticChamberSupport810.size1 (QuarticChamberSupportSize1810.cG0 ⟨hA, hBz, hCz, hDz, hEz, hFz, hGne⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BC`. -/
theorem quarticChamberSupport810_of_live_BC
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBC0 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBC1 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBC2 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BD`. -/
theorem quarticChamberSupport810_of_live_BD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht0a | ht0b | ht0c
  · -- D.natDegree < A.natDegree + B.natDegree
    rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBD1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBD2 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBD0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, by omega⟩)
  · -- D.natDegree = A.natDegree + B.natDegree
    rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBD1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  · -- D.natDegree > A.natDegree + B.natDegree
    rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBD1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BE`. -/
theorem quarticChamberSupport810_of_live_BE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBE1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBE2 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBE0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, by omega⟩)
  · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBE1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBE1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BF`. -/
theorem quarticChamberSupport810_of_live_BF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * A.natDegree + B.natDegree < F.natDegree
    rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF4 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 2 * A.natDegree + B.natDegree = F.natDegree
    rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF3 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 2 * A.natDegree + B.natDegree > F.natDegree
    rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF1 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF2 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBF0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BG`. -/
theorem quarticChamberSupport810_of_live_BG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht0a | ht0b | ht0c
  · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
    rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG4 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG0 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
    rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG3 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG0 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
    rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG1 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG2 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cBG0 ⟨hA, hBne, hCz, hDz, hEz, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CD`. -/
theorem quarticChamberSupport810_of_live_CD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
    rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCD1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCD2 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCD0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, by omega⟩)
  · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
    rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCD1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
    rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCD1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CE`. -/
theorem quarticChamberSupport810_of_live_CE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht0a | ht0b | ht0c
  · -- E.natDegree < A.natDegree + C.natDegree
    rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCE1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCE2 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCE0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, by omega⟩)
  · -- E.natDegree = A.natDegree + C.natDegree
    rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCE1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  · -- E.natDegree > A.natDegree + C.natDegree
    rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCE1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CF`. -/
theorem quarticChamberSupport810_of_live_CF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
    rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF4 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
    rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF3 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
    rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF1 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF2 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCF0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CG`. -/
theorem quarticChamberSupport810_of_live_CG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * A.natDegree + C.natDegree < G.natDegree
    rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG4 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG0 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 2 * A.natDegree + C.natDegree = G.natDegree
    rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG3 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · exact (by omega : False).elim
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG0 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 2 * A.natDegree + C.natDegree > G.natDegree
    rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG1 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG2 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cCG0 ⟨hA, hBz, hCne, hDz, hEz, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DE`. -/
theorem quarticChamberSupport810_of_live_DE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDE0 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDE1 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDE2 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DF`. -/
theorem quarticChamberSupport810_of_live_DF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDF0 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDF1 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDF2 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DG`. -/
theorem quarticChamberSupport810_of_live_DG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDG0 ⟨hA, hBz, hCz, hDne, hEz, hFz, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDG1 ⟨hA, hBz, hCz, hDne, hEz, hFz, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cDG2 ⟨hA, hBz, hCz, hDne, hEz, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `EF`. -/
theorem quarticChamberSupport810_of_live_EF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEF0 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEF1 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGz, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEF2 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `EG`. -/
theorem quarticChamberSupport810_of_live_EG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEG0 ⟨hA, hBz, hCz, hDz, hEne, hFz, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEG1 ⟨hA, hBz, hCz, hDz, hEne, hFz, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cEG2 ⟨hA, hBz, hCz, hDz, hEne, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `FG`. -/
theorem quarticChamberSupport810_of_live_FG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cFG0 ⟨hA, hBz, hCz, hDz, hEz, hFne, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cFG1 ⟨hA, hBz, hCz, hDz, hEz, hFne, hGne, by omega⟩)
  · exact QuarticChamberSupport810.size2 (QuarticChamberSupportSize2810.cFG2 ⟨hA, hBz, hCz, hDz, hEz, hFne, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCD`. -/
theorem quarticChamberSupport810_of_live_BCD
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD6 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCD3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCE`. -/
theorem quarticChamberSupport810_of_live_BCE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE6 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCE3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCF`. -/
theorem quarticChamberSupport810_of_live_BCF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + B.natDegree < F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF12 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree = F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF7 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree > F.natDegree
      rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF2 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF3 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + B.natDegree < F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF12 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree = F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF6 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree > F.natDegree
      rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF4 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF5 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF12 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF8 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF11 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF8 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF9 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF10 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCF8 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCG`. -/
theorem quarticChamberSupport810_of_live_BCG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht1a | ht1b | ht1c
    · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG12 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG0 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG7 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG0 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG2 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG3 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG0 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht1a | ht1b | ht1c
    · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG12 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG1 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG6 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG1 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG4 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG5 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG1 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + C.natDegree < G.natDegree
      rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG12 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG8 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 2 * A.natDegree + C.natDegree = G.natDegree
      rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG11 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG8 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
    · -- 2 * A.natDegree + C.natDegree > G.natDegree
      rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG9 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG10 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBCG8 ⟨hA, hBne, hCne, hDz, hEz, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDE`. -/
theorem quarticChamberSupport810_of_live_BDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE4 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE6 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDE5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDF`. -/
theorem quarticChamberSupport810_of_live_BDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht0a | ht0b | ht0c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF8 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF10 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF6 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF10 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF6 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF10 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF6 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * D.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDF1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDG`. -/
theorem quarticChamberSupport810_of_live_BDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG7 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG8 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG3 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG4 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG2 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG7 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG3 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG7 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG3 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG9 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG5 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG2 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG9 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG5 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG9 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * B.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG5 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht1a | ht1b | ht1c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG10 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG6 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG2 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG0 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
    · -- D.natDegree = A.natDegree + B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG10 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG6 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- D.natDegree > A.natDegree + B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG10 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 4 * B.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG6 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (B.natDegree + D.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBDG1 ⟨hA, hBne, hCz, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BEF`. -/
theorem quarticChamberSupport810_of_live_BEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF8 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF10 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF6 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF10 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF6 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + B.natDegree < F.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF10 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree = F.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + E.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF6 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (B.natDegree + E.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEF1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BEG`. -/
theorem quarticChamberSupport810_of_live_BEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht0a | ht0b | ht0c
  · -- G.natDegree < A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG7 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG8 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG3 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG4 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG2 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG7 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG3 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG7 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG3 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- G.natDegree = A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG9 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG5 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG2 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG9 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG5 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG9 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree) (E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG5 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- G.natDegree > A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG10 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG6 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG2 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG0 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
    · -- 2 * E.natDegree = 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG10 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG6 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * E.natDegree > 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG10 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 2 * B.natDegree + E.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG6 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * E.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBEG1 ⟨hA, hBne, hCz, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BFG`. -/
theorem quarticChamberSupport810_of_live_BFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + B.natDegree < F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG10 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree = F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG6 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree > F.natDegree
      rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG1 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG2 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + B.natDegree < F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG11 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree = F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 6 * B.natDegree) (4 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG5 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + B.natDegree > F.natDegree
      rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG3 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG4 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht1a | ht1b | ht1c
    · -- 5 * A.natDegree + 2 * B.natDegree < 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG12 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree = 2 * G.natDegree
      rcases lt_trichotomy (7 * A.natDegree + 6 * B.natDegree) (4 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG9 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG7 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG8 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cBFG0 ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDE`. -/
theorem quarticChamberSupport810_of_live_CDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE4 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE6 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDE5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGz, by omega⟩)
      · exact (by omega : False).elim
      · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDF`. -/
theorem quarticChamberSupport810_of_live_CDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht0a | ht0b | ht0c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF8 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF10 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF6 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF10 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF6 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF10 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF6 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (C.natDegree + D.natDegree) (A.natDegree + F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDF1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDG`. -/
theorem quarticChamberSupport810_of_live_CDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG7 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG8 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG3 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG4 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG2 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG7 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG3 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG7 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG3 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG9 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG5 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG2 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG9 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG5 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG9 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG5 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG10 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG6 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG2 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG0 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
    · -- 2 * D.natDegree = A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG10 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG6 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- 2 * D.natDegree > A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG10 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 4 * C.natDegree + 2 * D.natDegree) (4 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG6 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * D.natDegree) (A.natDegree + 2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCDG1 ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CEF`. -/
theorem quarticChamberSupport810_of_live_CEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF8 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht2a | ht2b | ht2c
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF10 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF6 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF10 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF6 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
        rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF10 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
        rcases lt_trichotomy (2 * C.natDegree + E.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF6 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * E.natDegree) (3 * A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEF1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CEG`. -/
theorem quarticChamberSupport810_of_live_CEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht0a | ht0b | ht0c
  · -- G.natDegree < A.natDegree + E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG7 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG8 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG3 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG4 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG2 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG7 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG3 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG7 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG3 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- G.natDegree = A.natDegree + E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG9 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG5 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG2 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG9 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG5 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- C.natDegree + G.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG9 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG5 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
  · -- G.natDegree > A.natDegree + E.natDegree
    rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht1a | ht1b | ht1c
    · -- E.natDegree < A.natDegree + C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG10 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG6 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG2 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG0 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
    · -- E.natDegree = A.natDegree + C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG10 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG6 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
    · -- E.natDegree > A.natDegree + C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * A.natDegree + C.natDegree < G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG10 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree = G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + E.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG6 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (C.natDegree + E.natDegree) (A.natDegree + G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCEG1 ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · exact (by omega : False).elim
        · exact (by omega : False).elim

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CFG`. -/
theorem quarticChamberSupport810_of_live_CFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG10 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG6 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG1 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG2 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 3 * A.natDegree + 2 * C.natDegree < 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG11 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree = 2 * F.natDegree
      rcases lt_trichotomy (A.natDegree + 3 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG5 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
      rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG3 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG4 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * A.natDegree + C.natDegree < G.natDegree
      rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG12 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + C.natDegree = G.natDegree
      rcases lt_trichotomy (2 * A.natDegree + 3 * C.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG9 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact (by omega : False).elim
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
    · -- 2 * A.natDegree + C.natDegree > G.natDegree
      rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG7 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG8 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cCFG0 ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DEF`. -/
theorem quarticChamberSupport810_of_live_DEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF3 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF6 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF2 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF1 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF6 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF5 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEF6 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGz, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DEG`. -/
theorem quarticChamberSupport810_of_live_DEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG0 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG3 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG6 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG2 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG1 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG6 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG4 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG5 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDEG6 ⟨hA, hBz, hCz, hDne, hEne, hFz, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `DFG`. -/
theorem quarticChamberSupport810_of_live_DFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG0 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG2 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG4 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG0 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG1 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG5 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG0 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG3 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cDFG6 ⟨hA, hBz, hCz, hDne, hEz, hFne, hGne, by omega⟩)

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `EFG`. -/
theorem quarticChamberSupport810_of_live_EFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG0 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG2 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG4 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG0 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG1 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG5 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG0 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG3 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size3 (QuarticChamberSupportSize3810.cEFG6 ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, by omega⟩)


end QuarticChamberExhaust810

end Max11DegreeRoutes
