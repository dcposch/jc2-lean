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
/-- Unowned chamber `DEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `N₅` face `F.natDegree + G.natDegree`. -/
theorem quarticChamberDEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG1810 A B C D E F G)
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
  have hdpos : 0 < F.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < F.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * F.natDegree < F.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq2; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * E.natDegree < F.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * D.natDegree < F.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAC hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ G.natDegree < F.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < F.natDegree + G.natDegree ∧ E.natDegree < F.natDegree + G.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hCn hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hrest : (n5QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < F.natDegree + G.natDegree :=
    n5QuarticChamberRest5000810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hAD hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq2 hApos; omega)) hztheta
  have hlead : (n5QuarticChamberFace5000810 A B C D E F G).natDegree =
      F.natDegree + G.natDegree :=
    n5QuarticChamberFace5000810_natDegree A B C D E F G hFne hGne
  have hle := degreeZeroN5Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hdpos hle; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
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
/-- Unowned chamber `DEFG` / `EE·EF·EG·FF·FG·GG` dies on the `N₂` face `E.natDegree + F.natDegree`. -/
theorem quarticChamberDEFG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberDEFG9810 A B C D E F G)
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
  have hdpos : 0 < E.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * D.natDegree < E.natDegree + F.natDegree ∧ D.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ 2 * E.natDegree < E.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0 hcq1 hcq7; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ 2 * D.natDegree < E.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0 hcq1 hcq7; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ G.natDegree < E.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < E.natDegree + F.natDegree ∧ E.natDegree < E.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hCn hcq0; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hCn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0; omega)
      · exact Or.inr (by clear * - h hAE hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hApos; omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < E.natDegree + F.natDegree) := by
    rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hCn hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAD hBn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hBn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hAD hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hAE hCn hcq0 hApos; omega)
    · exact Or.inr (by clear * - h hAE hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hCn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAC hBn hcq0 hcq7 hApos; omega)
    · exact Or.inr (by clear * - h hAB hAE hBn hcq0; omega)
    · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq7; omega)
    · exact Or.inr (by clear * - h hBn hcq0 hcq7 hApos; omega)
  have hrest : (n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + F.natDegree :=
    n2QuarticChamberRest5002810_natDegree_lt_of_live_DEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz (by clear * - hcq0 hcq1 hcq7; omega) hzl hzbeta hzdelta (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) hztheta
  have hlead : (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree :=
    n2QuarticChamberFace5002810_natDegree A B C D E F G hEne hFne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hCn hdpos hle; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG` dies on the `N₂` face `D.natDegree + G.natDegree`. -/
theorem quarticChamberBCDFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hrest : (n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest5001810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq1 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq10; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq10; omega) (by clear * - hcq0 hcq1 hcq4 hcq10; omega) (by clear * - hcq0 hcq1 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega))
  have hlead : (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    n2QuarticChamberFace5001810_natDegree A B C D E F G hDne hGne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdpos hle; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBCDFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG14810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq9 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hApos; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq2 hcq9; omega) (by clear * - hcq0 hcq8 hcq9; omega) (by clear * - hcq0 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdpos hkap; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG` dies on the `κ` face `C.natDegree + F.natDegree`. -/
theorem quarticChamberBCDFG45810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDFG45810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq15; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq15; omega)
  have hrest : (kappaQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest5002810_natDegree_lt_of_live_BCDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz (by clear * - hcq0 hcq2 hcq8 hcq15; omega) (by clear * - hcq0 hcq8 hcq15; omega) (by clear * - hcq0 hcq2 hcq8 hcq15; omega) (by clear * - hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq15; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq8 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq15; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8 hcq15; omega))
  have hlead : (kappaQuarticChamberFace5002810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace5002810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hEn hdpos hkap; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG` dies on the `N₂` face `E.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree ∧ 4 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 4 * B.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * B.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 3 * C.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ 2 * E.natDegree < E.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < E.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * C.natDegree < E.natDegree + F.natDegree ∧ G.natDegree < E.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq3 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq10; omega)
  have hrest : (n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + F.natDegree :=
    n2QuarticChamberRest5002810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq1 hcq3 hcq4 hcq10; omega) (by clear * - hcq1 hcq3 hcq4 hcq10; omega) (by clear * - hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos hcq10; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos; omega))
  have hlead : (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree :=
    n2QuarticChamberFace5002810_natDegree A B C D E F G hEne hFne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdpos hle; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
