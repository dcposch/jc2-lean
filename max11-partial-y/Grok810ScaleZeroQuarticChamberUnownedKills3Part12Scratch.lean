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
