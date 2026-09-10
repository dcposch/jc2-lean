import Grok810ScaleZeroQuarticChamberFacesScratch
import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberRestsScratch
import Grok810ScaleZeroQuarticChamberKillsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Scratch
import Grok810ScaleZeroQuarticChamberNuFacesScratch
import Grok810ScaleZeroQuarticChamberColumns3Scratch
import Grok810ScaleZeroQuarticChamberRests3Scratch
import Grok810ScaleZeroQuarticChamberKills3Scratch
import Grok810ScaleZeroQuarticChamberRests4Scratch
import Grok810ScaleZeroQuarticChamberInnerScratch
import Grok810ScaleZeroQuarticChamberKills4Scratch
import Grok810ScaleZeroQuarticChamberColumns5Scratch
import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsScratch
import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticChamberInfraN2Scratch
import Grok810ScaleZeroQuarticChamberInfraN3Scratch
import Grok810ScaleZeroQuarticChamberInfraN4Scratch
import Grok810ScaleZeroQuarticChamberInfraN5Scratch
import Grok810ScaleZeroQuarticChamberInfraN6Scratch
import Grok810ScaleZeroQuarticChamberInfraN7Scratch
import Grok810ScaleZeroQuarticChamberInfraOmicronScratch
import Grok810ScaleZeroQuarticChamberInfraPrimitiveScratch
import Grok810ScaleZeroQuarticChamberN5CostLadderScratch
import Grok810ScaleZeroQuarticChamberN7BandsScratch
import Grok810ScaleZeroQuarticChamberUnownedPacketsScratch
import Grok810ScaleZeroQuarticChamberUnownedColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedRests3Scratch
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
/-- Unowned chamber `BCDEFG` / `CG·DD·CCC` leaf 9 dies on the `ξ` face `C.natDegree + 2 * D.natDegree`. -/
theorem quarticRefinedBCDEFG102L9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < C.natDegree + 2 * D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + G.natDegree < C.natDegree + 2 * D.natDegree ∧ E.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < C.natDegree + 2 * D.natDegree ∧ C.natDegree + F.natDegree < C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < C.natDegree + 2 * D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq6 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq5 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
      · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq6 hcq7 hx10 hx11 hx12; omega)
  have hrest : (xiQuarticChamberRest5003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberRest5003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12; omega) (by omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12; omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hx10 hx11 hx12; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq2 hx10 hx11 hx12; omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq3 hcq5 hx10 hx11 hx12; omega) (by omega) (by omega) (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq4 hx10 hx11 hx12; omega) hzl hzbeta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hx10 hx11 hx12 hApos; omega)) (Or.inr (by omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq5 hcq7 hx10 hx11 hx12 hApos; omega)) (Or.inr (by clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hcq0 hcq1 hcq3 hcq7 hx10 hx11 hx12; omega))
  have hlead : (xiQuarticChamberFace5003810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree :=
    xiQuarticChamberFace5003810_natDegree A B C D E F G hCne hDne
  rw [degreeZeroXiQuartic810_eq_face5003_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdpos hxi; omega


end QuarticChamberUnownedKills4810

end Max11DegreeRoutes
