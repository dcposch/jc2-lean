import Grok810ScaleZeroQuarticChamberUnownedRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills1Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests4Scratch

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
/-- Unowned chamber `CDEFG` / `CF·CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEFG11810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG11810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq11; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq6 hcq11; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hcq11; omega)
  have hrest : (xiQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest5002810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq3; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega) (by clear * - hcq0 hcq1 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hcq11; omega))
  have hlead : (xiQuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace5002810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hxi; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
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
/-- Unowned chamber `CDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` dies on the `N₂` face `E.natDegree + F.natDegree`. -/
theorem quarticChamberCDEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG13810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < E.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree ∧ 4 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * D.natDegree < E.natDegree + F.natDegree ∧ 3 * C.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ D.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ 2 * E.natDegree < E.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * D.natDegree < E.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * C.natDegree < E.natDegree + F.natDegree ∧ G.natDegree < E.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ E.natDegree < E.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq11; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
  have hrest : (n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + F.natDegree :=
    n2QuarticChamberRest5002810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq1 hcq8 hcq11; omega) (by clear * - hcq0 hcq1 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq2 hcq8 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq8 hApos; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq2 hcq8 hApos; omega))
  have hlead : (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree :=
    n2QuarticChamberFace5002810_natDegree A B C D E F G hEne hFne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hle; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
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
/-- Unowned chamber `CDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `D.natDegree + E.natDegree`. -/
theorem quarticChamberCDEFG39810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG39810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos hcq10; omega)
  have hzzeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hApos hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hAD hcq0; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq0 hcq2 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hApos hcq10; omega)
  have hrest : (kappaQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest5000810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq0 hcq1 hcq2 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq10; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos hcq10; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq2 hApos hcq10; omega))
  have hlead : (kappaQuarticChamberFace5000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace5000810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hkap; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `N₅` face `F.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < F.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree ∧ 5 * A.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 4 * B.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 3 * C.natDegree < F.natDegree + G.natDegree ∧ 3 * B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + D.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * C.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ C.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * F.natDegree < F.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 4 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 3 * C.natDegree < F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * E.natDegree < F.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * D.natDegree < F.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq5 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega)
  have hrest : (n5QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < F.natDegree + G.natDegree :=
    n5QuarticChamberRest5000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq0 hcq1 hcq5 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq5 hcq14; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hApos hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hApos hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq5 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq5 hApos; omega))
  have hlead : (n5QuarticChamberFace5000810 A B C D E F G).natDegree =
      F.natDegree + G.natDegree :=
    n5QuarticChamberFace5000810_natDegree A B C D E F G hFne hGne
  have hle := degreeZeroN5Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdpos hle; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG` dies on the `N₂` face `D.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG13810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 4 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ 2 * E.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq12 hcq14; omega)
  have hrest : (n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest5001810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq0 hcq4 hcq12 hcq14; omega) (by clear * - hcq0 hcq1 hcq4 hcq14; omega) (by clear * - hcq0 hcq1 hcq14; omega) (by clear * - hcq0 hcq4 hcq12; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq12 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos hcq12; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hApos; omega))
  have hlead : (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    n2QuarticChamberFace5001810_natDegree A B C D E F G hDne hGne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdpos hle; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
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
/-- Unowned chamber `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG` dies on the `N₂` face `E.natDegree + F.natDegree`. -/
theorem quarticChamberBCDEFG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG16810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < E.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree ∧ 4 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 4 * B.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * D.natDegree < E.natDegree + F.natDegree ∧ 2 * B.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < E.natDegree + F.natDegree ∧ 3 * C.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ D.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ 2 * E.natDegree < E.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq11 hcq14; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * D.natDegree < E.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq11 hcq14; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < E.natDegree + F.natDegree ∧ 2 * C.natDegree < E.natDegree + F.natDegree ∧ G.natDegree < E.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq11 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq4 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq4 hcq11 hcq14; omega)
  have hrest : (n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + F.natDegree :=
    n2QuarticChamberRest5002810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq1 hcq4 hcq11 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq1 hcq3 hcq4 hcq14; omega) (by clear * - hcq14; omega) (by clear * - hcq1 hcq4 hcq11 hcq14; omega) (by clear * - hcq1 hcq4 hcq11 hcq14; omega) (by clear * - hcq0 hcq4 hcq11; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos hcq11 hcq14; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq3 hcq4 hApos hcq11; omega)) (Or.inr (by clear * - hcq1 hcq3 hcq4 hApos hcq11; omega))
  have hlead : (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree :=
    n2QuarticChamberFace5002810_natDegree A B C D E F G hEne hFne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdpos hle; omega

end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
