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

/-! # Unowned single-carrier kills, part 5/5

1 of the 85 chambers `UNOWNED_CHAMBERS.md` closes with a
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

section QuarticChamberUnownedKills5810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEFG` / `CG·EE·CCC` leaf 0 dies on the `N₂` face `B.natDegree + C.natDegree + E.natDegree`. -/
theorem quarticRefinedBCDEFG108L0810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG108L0810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13, hq14, hq15, hq16, hq17, hq18, hq19, hq20, hq21, hq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hdpos : 0 < B.natDegree + C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 4 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 4 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * D.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ D.natDegree + F.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * E.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * D.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ G.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ 2 * B.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ E.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < B.natDegree + C.natDegree + E.natDegree ∧ C.natDegree < B.natDegree + C.natDegree + E.natDegree) := by
    rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hrest : (n2QuarticChamberRest5003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + C.natDegree + E.natDegree :=
    n2QuarticChamberRest5003810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hzl hzbeta (Or.inr (by omega)) hzdelta (Or.inr (by omega)) hzzeta (Or.inr (by omega)) hztheta
  have hlead : (n2QuarticChamberFace5003810 A B C D E F G).natDegree =
      B.natDegree + C.natDegree + E.natDegree :=
    n2QuarticChamberFace5003810_natDegree A B C D E F G hBne hCne hEne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5003_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega


end QuarticChamberUnownedKills5810

end Max11DegreeRoutes
