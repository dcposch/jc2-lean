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
/-- Unowned chamber `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG` dies on the `N₅` face `F.natDegree + G.natDegree`. -/
theorem quarticChamberBCDEFG81810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDEFG81810 A B C D E F G)
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
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 4 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ 3 * C.natDegree < F.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ 2 * E.natDegree < F.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < F.natDegree + G.natDegree ∧ 2 * B.natDegree + C.natDegree < F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < F.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < F.natDegree + G.natDegree ∧ C.natDegree + E.natDegree < F.natDegree + G.natDegree ∧ 2 * D.natDegree < F.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < F.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq21; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq12 hcq21; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)
  have hrest : (n5QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < F.natDegree + G.natDegree :=
    n5QuarticChamberRest5000810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos (by clear * - hcq0 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq1 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq1 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq12 hcq21; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega) (by clear * - hcq0 hcq3 hcq21; omega) (by clear * - hcq0 hcq2 hcq3 hcq21; omega) (by clear * - hcq0 hcq1 hcq21; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq12 hcq21; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq12 hcq21; omega))
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
