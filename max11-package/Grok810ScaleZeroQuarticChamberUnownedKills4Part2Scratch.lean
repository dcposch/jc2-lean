import Grok810ScaleZeroQuarticChamberUnownedRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills1Scratch

/-! # Unowned single-carrier kills, part 4/5

19 of the 85 chambers `UNOWNED_CHAMBERS.md` closes with a
single-monomial face, after the carrier change (including `N₂, N₃,
`N₅`, `N₆`) and the `n5-cost`/`n7-cost` bands.  A column marked
`*-hnc` is discharged by `by_contra` plus the chamber's ℕ conjuncts,
which force every letter constant and contradict `hnc`.
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

section QuarticChamberUnownedKills4810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEFG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEFG25810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG25810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq7 hcq10 hcq11; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq7 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq5 hcq7 hcq10 hcq11; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree ∧ D.natDegree + E.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq7 hcq10 hcq11; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq1 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq1 hcq10 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq1 hcq7 hcq11; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq5 hcq7 hcq10 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq5 hcq7 hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq10 hcq11; omega)) (Or.inr (by clear * - hcq1 hcq10 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq10 hcq11; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hpi; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
