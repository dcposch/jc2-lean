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
