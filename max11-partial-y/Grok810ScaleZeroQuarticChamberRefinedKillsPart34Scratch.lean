import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart10Scratch

/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
/-- Refined leaf 1 of chamber `CDEFG` / `CG·DD·CCC` dies on the single-monomial `ξ` face. -/
theorem quarticRefinedCDEFG28L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedCDEFG28L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4⟩ := hch
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hBn hcq0 hcq1 hcq2 hrf0 hrf1 hzero; omega)
  have hz0l : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1; omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1; omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq4 hcq5; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq5; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq5; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1; omega)
  have hr0 : (xiQuarticChamberRest1810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberRest1810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hBz (by clear * - hrf1; omega) (by clear * - hcq0 hcq1 hrf0 hrf1; omega) (by clear * - hcq0 hrf0 hrf1; omega) (by clear * - hcq0 hcq1 hcq5 hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hrf1 hApos; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1; omega)) (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hrf0 hrf1 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hrf1; omega))
  have hlead : (xiQuarticChamberFace1810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberFace1810_natDegree A B C D E F G hCne hDne
  rw [degreeZeroXiQuartic810_eq_face1_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdp0 hxi; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
