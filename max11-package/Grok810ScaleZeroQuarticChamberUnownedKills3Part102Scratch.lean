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
/-- Unowned chamber `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBCEFG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG14810 A B C D E F G)
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
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ 2 * C.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq11; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq2 hcq11; omega) (by clear * - hcq0 hcq2 hcq8 hcq11; omega) (by clear * - hcq0 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq11; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdpos hkap; omega

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
/-- Unowned chamber `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `C.natDegree + F.natDegree`. -/
theorem quarticChamberBCEFG45810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCEFG45810 A B C D E F G)
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
  have hdpos : 0 < C.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq12 hcq14; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8 hcq14; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq14; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hcq14; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8 hApos hcq14; omega)
  have hrest : (kappaQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest5002810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hDz (by clear * - hcq0 hcq8 hcq14; omega) (by clear * - hcq0 hcq8 hcq14; omega) (by clear * - hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hApos hcq14; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8 hcq14; omega)) (Or.inr (by clear * - hcq0 hcq8 hcq14; omega))
  have hlead : (kappaQuarticChamberFace5002810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace5002810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdpos hkap; omega

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
/-- Unowned chamber `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `N₅` face `F.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < F.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 4 * B.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 3 * B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + D.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ E.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ 2 * F.natDegree < F.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 4 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * E.natDegree < F.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * D.natDegree < F.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq3 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq13; omega)
  have hrest : (n5QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < F.natDegree + G.natDegree :=
    n5QuarticChamberRest5000810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) (by clear * - hcq0 hcq2 hcq3 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq13; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq13; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos hcq13; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hApos; omega))
  have hlead : (n5QuarticChamberFace5000810 A B C D E F G).natDegree =
      F.natDegree + G.natDegree :=
    n5QuarticChamberFace5000810_natDegree A B C D E F G hFne hGne
  have hle := degreeZeroN5Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdpos hle; omega

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
/-- Unowned chamber `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG10810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG10810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq10 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos hcq10; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq11; omega) (by clear * - hcq0 hcq2 hcq11; omega) (by clear * - hcq0 hcq1 hcq2 hcq10; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdpos hkap; omega

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
/-- Unowned chamber `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBDEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG13810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq9 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq9 hcq13; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq13; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq13; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hcq0 hcq2 hcq13; omega) (by clear * - hcq0 hcq2 hcq9 hcq13; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdpos hkap; omega

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
/-- Unowned chamber `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `D.natDegree + E.natDegree`. -/
theorem quarticChamberBDEFG39810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDEFG39810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hdpos : 0 < D.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq9; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq9; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq2; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAB hCn hcq0 hApos hcq13; omega)
      · exact Or.inr (by clear * - h hAB hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAD hcq0 hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq9 hApos; omega)
  have hrest : (kappaQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest5000810_natDegree_lt_of_live_BDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz (by clear * - hAD hcq0 hcq1 hcq9; omega) (by clear * - hAD hcq0 hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq9 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq9 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq9 hApos; omega))
  have hlead : (kappaQuarticChamberFace5000810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace5000810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hCn hdpos hkap; omega

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
/-- Unowned chamber `CDEFG` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG1810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq6 hcq8 hcq11; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq6 hcq8 hcq11; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq3 hcq11; omega)
      · exact Or.inr (by clear * - h hcq6 hcq11; omega)
      · exact Or.inr (by clear * - h hcq8 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq3 hApos hcq11; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq1 hcq11; omega) (by clear * - hcq11; omega) (by clear * - hcq0 hcq11; omega) (by clear * - hcq3 hcq11; omega) (by clear * - hcq5 hcq11; omega) (by clear * - hcq2 hcq3 hcq11; omega) (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq2 hcq5 hcq6 hApos hcq11; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq1 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq0 hcq2 hApos hcq11; omega)) (Or.inr (by clear * - hcq1 hApos hcq11; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hpi; omega

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
/-- Unowned chamber `CDEFG` / `CF·CG·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberCDEFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEFG5810 A B C D E F G)
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
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq11; omega)
  have hrest : (xiQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest5001810_natDegree_lt_of_live_CDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz (by clear * - hcq1 hcq2 hcq11; omega) (by clear * - hcq0 hcq4 hcq11; omega) (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq4; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq11; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq11; omega)) (Or.inr (by clear * - hcq1 hcq2 hcq11; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq4 hcq11; omega))
  have hlead : (xiQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace5001810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hApos hAB hAC hAD hAE hAF hAG hBn hdpos hxi; omega

end QuarticChamberUnownedKills3810

end Max11DegreeRoutes
