import Grok810ScaleZeroQuarticChamberUnownedRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills1Scratch

/-! # Unowned single-carrier kills, part 3/5

17 of the 85 chambers `UNOWNED_CHAMBERS.md` closes with a
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

section QuarticChamberUnownedKills3810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `DEFG` / `DD·DF·DG·FF·FG·GG` dies on the `N₂` face `D.natDegree + G.natDegree`. -/
theorem quarticChamberDEFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq8; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq1 hcq8; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq8 hApos; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree ∧ E.natDegree < D.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAC hAD hBn hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq8 hApos; omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < D.natDegree + G.natDegree) := by
    rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAD hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq1 hcq8 hApos; omega)
    · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hAC hAD hCn hcq1; omega)
    · exact Or.inr (by clear * - h hBn hcq1 hcq8 hApos; omega)
  have hrest : (n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest5001810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq0 hcq1 hcq8; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq8 hApos; omega)) hztheta
  have hlead : (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    n2QuarticChamberFace5001810_natDegree A B C D E F G hDne hGne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hdpos hle; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
