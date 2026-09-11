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
