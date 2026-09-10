import Grok810ScaleZeroQuarticChamberExhaust2Part14Scratch

/-! Part 15 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
end
