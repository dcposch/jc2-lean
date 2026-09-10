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

/-! # Unowned single-carrier kills, part 2/5

23 of the 85 chambers `UNOWNED_CHAMBERS.md` closes with a
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

section QuarticChamberUnownedKills2810

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `EFG` / `EE·EF·EG·FF·FG·GG` dies on the `N₆` face `A.natDegree + F.natDegree + G.natDegree`. -/
theorem quarticChamberEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberEFG1810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + F.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hcon; omega)
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (8 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 5 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (8 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0 hcq1; omega)
  have hzbeta : beta = 0 ∨ (7 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * F.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (7 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hAE hcq0; omega)
  have hzdelta : delta = 0 ∨ (6 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * E.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (6 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hzzeta : zeta = 0 ∨ (5 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (5 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hAE hBn hDn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hAE hDn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hztheta : theta = 0 ∨ (4 * A.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + F.natDegree + G.natDegree ∧ G.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
    have hbthetas : theta = 0 ∨ (4 * A.natDegree < A.natDegree + F.natDegree + G.natDegree) := by
      rcases h7btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAE hDn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAC hBn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hApos; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hApos; omega)
  have hrest : (n6QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + F.natDegree + G.natDegree :=
    n6QuarticChamberRest5000810_natDegree_lt_of_live_EFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hCz hDz hzl hzbeta (Or.inr (by clear * - hcq1 hApos; omega)) hzdelta hzzeta (Or.inr (by clear * - hcq1 hApos; omega)) hztheta
  have hlead : (n6QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + F.natDegree + G.natDegree :=
    n6QuarticChamberFace5000810_natDegree A B C D E F G hAne hFne hGne
  have hle := degreeZeroN6Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos hprim homi hnu
  rw [degreeZeroN6Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hApos hAB hAC hAD hAE hAF hAG hBn hCn hDn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberBCDG17810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG17810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ 5 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 3 * C.natDegree < 2 * G.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * G.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * G.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq9; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq2 hcq9; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq9; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq1 hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq9; omega) (by clear * - hcq1 hcq2 hcq9; omega) (by clear * - hcq9; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq9; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDG` / `DD·CCC` dies on the `N₂` face `2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberBCDG24810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG24810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 4 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq10; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq10; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * C.natDegree + D.natDegree ∧ B.natDegree + D.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq9 hcq10; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < 2 * C.natDegree + D.natDegree ∧ 2 * B.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq3 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq2 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
  have hztheta : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree ∧ C.natDegree < 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (2 * A.natDegree < 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq2 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9; omega)
      · exact Or.inr (by clear * - h hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq9 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq9 hcq10; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq6 hcq9; omega)
  have hrest : (n2QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + D.natDegree :=
    n2QuarticChamberRest5000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hEz hFz (by clear * - hcq0 hcq6; omega) (by clear * - hcq0 hcq6 hcq9; omega) (by clear * - hcq0 hcq9; omega) (by clear * - hcq0 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq6 hcq9 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq6 hcq9; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq6 hcq9; omega)) hztheta
  have hlead : (n2QuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + D.natDegree :=
    n2QuarticChamberFace5000810_natDegree A B C D E F G hCne hDne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hApos hAB hAC hAD hAE hAF hAG hEn hFn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBDFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBDFG7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hEn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree ∧ 2 * D.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAE hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq2 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hEn hdpos hkap; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG` dies on the `κ` face `B.natDegree + G.natDegree`. -/
theorem quarticChamberBEFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBEFG7810 A B C D E F G)
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
  obtain ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < B.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + G.natDegree ∧ B.natDegree + F.natDegree < B.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzbeta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + G.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + G.natDegree ∧ G.natDegree < B.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzdelta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree ∧ 2 * B.natDegree < B.natDegree + G.natDegree ∧ E.natDegree < B.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hCn hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAD hCn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAC hCn hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
  have hrest : (kappaQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + G.natDegree :=
    kappaQuarticChamberRest5001810_natDegree_lt_of_live_BEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hCz hDz (by clear * - hcq0 hcq2 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (kappaQuarticChamberFace5001810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree :=
    kappaQuarticChamberFace5001810_natDegree A B C D E F G hBne hGne
  rw [degreeZeroKappaQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hCn hDn hdpos hkap; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEF` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDEF1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEF1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hGn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq4 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq4 hcq5 hcq6; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq5 hcq6; omega)
      · exact absurd h (by clear * - hGn hApos; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq6 hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CDEF l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hGz (by clear * - hcq0 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq2 hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq1 hcq2 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq4 hcq6 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hGn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq5 hcq6; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq5 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq5 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq5 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq4 hcq5 hcq6; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq0 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq3 hcq6; omega) (by clear * - hcq0 hcq4 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq3 hcq4 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq5 hcq6; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDEG3810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG3810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq0 hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq6; omega) (by clear * - hcq1 hcq2 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hApos; omega)) (Or.inr (by clear * - hcq0 hcq6 hApos; omega)) (Or.inr (by clear * - hcq6; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCDEG9810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG9810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < E.natDegree + G.natDegree ∧ 2 * C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + G.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq6; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ D.natDegree + E.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq6; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < E.natDegree + G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq6; omega)
  have hrest : (xiQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest5002810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq6; omega) (by clear * - hcq0 hcq1 hcq4 hcq6; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6; omega))
  have hlead : (xiQuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace5002810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEG` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCDEG14810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG14810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAF hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hBn hFn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ E.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq7; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq7 hApos; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq0 hcq1; omega) (by clear * - hcq0 hcq2 hcq7; omega) (by clear * - hcq0 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDEG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCDEG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDEG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
  have hrest : (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest5000810_natDegree_lt_of_live_CDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hFz (by clear * - hcq0 hcq2 hcq8; omega) (by clear * - hcq0 hcq1; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq2 hcq8; omega))
  have hlead : (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace5000810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hFn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCDFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 3 * D.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq4 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact absurd h (by clear * - hEn hApos; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq7 hApos; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq1 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq2 hcq7; omega) (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CF·CG·DD` dies on the `ξ` face `A.natDegree + D.natDegree + F.natDegree`. -/
theorem quarticChamberCDFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + D.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 3 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ 2 * A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ A.natDegree + F.natDegree < A.natDegree + D.natDegree + F.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + D.natDegree + F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hrest : (xiQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberRest5001810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq3 hcq7; omega) (by clear * - hcq0 hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega))
  have hlead : (xiQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree :=
    xiQuarticChamberFace5001810_natDegree A B C D E F G hAne hDne hFne
  rw [degreeZeroXiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CF·CG·DD·DF·DG·FF·FG·GG` dies on the `N₂` face `D.natDegree + G.natDegree`. -/
theorem quarticChamberCDFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG7810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < D.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree ∧ 4 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * D.natDegree < D.natDegree + G.natDegree ∧ 3 * C.natDegree < D.natDegree + G.natDegree ∧ C.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ D.natDegree + F.natDegree < D.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + G.natDegree ∧ 2 * D.natDegree < D.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + G.natDegree ∧ 2 * C.natDegree < D.natDegree + G.natDegree ∧ G.natDegree < D.natDegree + G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hzzeta : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + G.natDegree) := by
    have hbzetas : zeta = 0 ∨ (3 * A.natDegree < D.natDegree + G.natDegree) := by
      rcases h7bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hAE hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hApos; omega)
  have hrest : (n2QuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + G.natDegree :=
    n2QuarticChamberRest5001810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq2 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega))
  have hlead : (n2QuarticChamberFace5001810 A B C D E F G).natDegree =
      D.natDegree + G.natDegree :=
    n2QuarticChamberFace5001810_natDegree A B C D E F G hDne hGne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq6 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq6 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq1 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq6 hcq7; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq1 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq6 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq6 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7; omega)) (Or.inr (by clear * - hcq1 hcq6 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq6 hcq7; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `CG·DD` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCDFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * D.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hEn hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq7; omega) (by clear * - hcq7; omega) (by clear * - hcq1; omega) (by clear * - hcq7; omega) (by clear * - hcq2 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq7 hApos; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq7 hApos; omega)) (Or.inr (by clear * - hcq7; omega)) (Or.inr (by clear * - hcq1 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDFG` / `DD·CCC` dies on the `N₃` face `A.natDegree + 2 * C.natDegree + D.natDegree`. -/
theorem quarticChamberCDFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hcon; omega)
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hzl : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq8; omega)
  have hzbeta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ D.natDegree + F.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq8; omega)
  have hzdelta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hEn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hzzeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbzetas : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5bzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hAE hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq8; omega)
  have hztheta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    have hbthetas : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
      rcases h5btheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq2 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq3; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hEn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq8; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq8; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq8; omega)
    rcases hbthetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
  have hrest : (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest5000810_natDegree_lt_of_live_CDFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hEz (by clear * - hcq0 hcq2; omega) (by clear * - hcq3; omega) (by clear * - hcq0 hcq8; omega) (by clear * - hcq0 hcq2 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hApos; omega)) hztheta
  have hlead : (n3QuarticChamberFace5000810 A B C D E F G).natDegree =
      A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberFace5000810_natDegree A B C D E F G hAne hCne hDne
  have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu
  rw [degreeZeroN3Quartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hEn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `CF` dies on the `π` face `A.natDegree + 2 * F.natDegree`. -/
theorem quarticChamberCEFG1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hdpos : 0 < A.natDegree + 2 * F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ 2 * C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ F.natDegree + G.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq2 hcq4 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ E.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq2 hcq4 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree ∧ C.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hApos; omega)
      · exact Or.inr (by clear * - h hcq7; omega)
      · exact absurd h (by clear * - hDn hApos; omega)
      · exact Or.inr (by clear * - h hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq4 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq7 hApos; omega)
  have hzzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < A.natDegree + 2 * F.natDegree) := by
    rcases hbzeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd hBz h
    · exact Or.inr (by clear * - h hcq7; omega)
    · exact absurd h (by clear * - hDn hApos; omega)
    · exact Or.inr (by clear * - h hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hApos; omega)
    · exact Or.inr (by clear * - h hcq0 hcq4 hcq7; omega)
  have hrest : (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * F.natDegree :=
    piQuarticChamberRest5001810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq7; omega) (by clear * - hcq0 hcq7; omega) (by clear * - hcq1 hcq7; omega) (by clear * - hcq0; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq7; omega)) hzzeta (Or.inr (by clear * - hcq0 hcq7; omega)) (Or.inr (by clear * - hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace5001810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree :=
    piQuarticChamberFace5001810_natDegree A B C D E F G hAne hFne
  rw [degreeZeroPiQuartic810_eq_face5001_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `CF·CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCEFG5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    · exact absurd h (by clear * - hDn hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hrest : (xiQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest5002810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq7; omega) (by clear * - hcq0 hcq1 hcq2; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq7; omega))
  have hlead : (xiQuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace5002810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `CF·CG·EE·EF·EG·FF·FG·GG` dies on the `N₂` face `E.natDegree + F.natDegree`. -/
theorem quarticChamberCEFG7810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG7810 A B C D E F G)
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
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + F.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨h7bl, h7bbeta, h7bdelta, h7bzeta, h7btheta⟩ :=
    quarticSigmaN7CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hprim homi hnu hkap
  have hzl : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree ∧ 4 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + C.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 3 * C.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ 2 * E.natDegree < E.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (6 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzbeta : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < E.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < E.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (5 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bbeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq7; omega)
  have hzdelta : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < E.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < E.natDegree + F.natDegree ∧ 2 * C.natDegree < E.natDegree + F.natDegree ∧ G.natDegree < E.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (4 * A.natDegree < E.natDegree + F.natDegree) := by
      rcases h7bdelta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
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
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq0 hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq2 hApos; omega)
      · exact Or.inr (by clear * - h hApos; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hBn hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAD hBn hcq1 hcq2 hcq7; omega)
      · exact Or.inr (by clear * - h hAB hBn hcq1 hcq2 hcq7; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq1 hcq2 hApos; omega)
  have hrest : (n2QuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + F.natDegree :=
    n2QuarticChamberRest5002810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz hzl hzbeta hzdelta (Or.inr (by clear * - hcq2 hApos; omega)) hzzeta (Or.inr (by clear * - hcq1 hcq2 hApos; omega))
  have hlead : (n2QuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + F.natDegree :=
    n2QuarticChamberFace5002810_natDegree A B C D E F G hEne hFne
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hle; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `CG` dies on the `π` face `2 * G.natDegree`. -/
theorem quarticChamberCEFG13810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG13810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + E.natDegree + F.natDegree < 2 * G.natDegree ∧ 2 * C.natDegree + F.natDegree < 2 * G.natDegree ∧ F.natDegree + G.natDegree < 2 * G.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq6 hcq7; omega)
  have hzbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * G.natDegree ∧ E.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq3 hcq6 hcq7; omega)
  have hzdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree ∧ C.natDegree + F.natDegree < 2 * G.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * G.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq3 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hcq7; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq6 hcq7; omega)
  have hrest : (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * G.natDegree :=
    piQuarticChamberRest5000810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq7; omega) (by clear * - hcq0; omega) (by clear * - hcq7; omega) (by clear * - hcq1 hcq7; omega) hzl hzbeta (Or.inr (by clear * - hcq1 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq1 hcq7; omega)) (Or.inr (by clear * - hcq0; omega)) (Or.inr (by clear * - hcq7; omega)) (Or.inr (by clear * - hcq0 hcq7 hApos; omega))
  have hlead : (piQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * G.natDegree :=
    piQuarticChamberFace5000810_natDegree A B C D E F G hGne
  rw [degreeZeroPiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hpi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hpi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `CG·EE` dies on the `ξ` face `E.natDegree + G.natDegree`. -/
theorem quarticChamberCEFG15810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG15810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < E.natDegree + G.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ E.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree ∧ C.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq3 hcq7; omega)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < E.natDegree + G.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq7; omega)
  have hrest : (xiQuarticChamberRest5002810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < E.natDegree + G.natDegree :=
    xiQuarticChamberRest5002810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq7; omega) (by clear * - hcq0 hcq1 hcq3; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq7; omega))
  have hlead : (xiQuarticChamberFace5002810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree :=
    xiQuarticChamberFace5002810_natDegree A B C D E F G hEne hGne
  rw [degreeZeroXiQuartic810_eq_face5002_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hxi; omega
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEFG` / `EE·CCC` dies on the `ξ` face `2 * C.natDegree + E.natDegree`. -/
theorem quarticChamberCEFG20810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG20810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hdpos : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hcon; omega)
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hzl : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ E.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (3 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
  have hzbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (2 * A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact absurd h (by clear * - hBn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact absurd h (by clear * - hDn hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq8; omega)
  have hzdelta : delta = 0 ∨ (A.natDegree + F.natDegree < 2 * C.natDegree + E.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by clear * - hBn hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    · exact absurd h (by clear * - hDn hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq8; omega)
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq8; omega)
  have hrest : (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest5000810_natDegree_lt_of_live_CEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdpos hBz hDz (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq1 hcq8; omega) hzl hzbeta (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) hzdelta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq8; omega))
  have hlead : (xiQuarticChamberFace5000810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree :=
    xiQuarticChamberFace5000810_natDegree A B C D E F G hCne hEne
  rw [degreeZeroXiQuartic810_eq_face5000_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hxi
  clear * - hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hApos hAB hAC hAD hAE hAF hAG hBn hDn hdpos hxi; omega


end QuarticChamberUnownedKills2810

end Max11DegreeRoutes
