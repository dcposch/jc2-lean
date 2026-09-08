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
import Grok810ScaleZeroQuarticChamberUnownedKills2Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills3Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills4Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests10Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests11Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges2Scratch

/-! # Unowned multi-carrier systems, part 3/15

7 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
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

section QuarticChamberUnownedSystems3810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BFG` / `BG·BBB`: the 5 face rows force `b * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBFG8810_cert
    (a b c d e f g : k)
    (hr0 : (5 / 512 : k) * a * b ^ 3 + (5 / 16 : k) * b * g = 0)
    (hr1 : (-5 / 4096 : k) * a ^ 2 * b ^ 3 + (-5 / 128 : k) * a * b * g = 0)
    (hr2 : (-5 / 65536 : k) * a ^ 3 * b ^ 3 + (-5 / 2048 : k) * a ^ 2 * b * g = 0)
    (hr3 : (15 / 4096 : k) * a ^ 2 * b ^ 4 + (5 / 64 : k) * a * b ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr4 : (-5 / 65536 : k) * a ^ 4 * b ^ 3 + (-5 / 2048 : k) * a ^ 3 * b * g = 0)
    (hBc : (b : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : b * g ^ 2 = 0 := by
    linear_combination ((-3 / 20 : k) * a * b ^ 2 + (8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * b) * hr3
  exact (mul_ne_zero hBc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BFG` / `BG·BBB` dies on the 5-carrier system (κ, ν, ο, π, Π). -/
theorem quarticChamberBFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCz, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < A.natDegree + 3 * B.natDegree := by
    omega
  have hdz0 : 0 < A.natDegree + 3 * B.natDegree := by omega
  have hz0l : l = 0 ∨ (5 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < A.natDegree + 3 * B.natDegree ∧ G.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz0theta : theta = 0 ∨ (A.natDegree < A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hr0 : (kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree :=
    kappaQuarticChamberRest6000810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hCz hDz hEz hz0l hz0beta (Or.inr (by omega)) hz0delta hz0zeta (Or.inr (by omega)) hz0theta
  have hct0 := kappaQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by omega)
  have hq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    omega
  rw [degreeZeroKappaQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz1 : 0 < 2 * A.natDegree + 3 * B.natDegree := by omega
  have hz1l : l = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + G.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz1zeta : zeta = 0 ∨ (3 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz1theta : theta = 0 ∨ (2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hr1 : (nuQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 3 * B.natDegree :=
    nuQuarticChamberRest6000810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hCz hDz hEz (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) hz1zeta (Or.inr (by omega)) hz1theta
  have hct1 := nuQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by omega)
  have hq1 : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnu]
    omega
  rw [degreeZeroNuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 3 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz2 : 0 < 3 * A.natDegree + 3 * B.natDegree := by omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree + G.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < 3 * A.natDegree + 3 * B.natDegree ∧ 2 * B.natDegree < 3 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hr2 : (omicronQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * A.natDegree + 3 * B.natDegree :=
    omicronQuarticChamberRest6000810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hCz hDz hEz (by omega) (by omega) (by omega) hz2l hz2beta (Or.inr (by omega)) hz2delta (Or.inr (by omega)) hz2zeta (Or.inr (by omega)) hz2theta
  have hct2 := omicronQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by omega)
  have hq2 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [homi]
    omega
  rw [degreeZeroOmicronQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by
    omega
  have hdz3 : 0 < 2 * A.natDegree + 4 * B.natDegree := by omega
  have hz3l : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 4 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 5 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ F.natDegree + G.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3beta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 3 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * B.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3delta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < 2 * A.natDegree + 4 * B.natDegree ∧ 2 * A.natDegree + F.natDegree < 2 * A.natDegree + 4 * B.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr3 : (piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 4 * B.natDegree :=
    piQuarticChamberRest6000810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hCz hDz hEz (by omega) (by omega) hz3l hz3beta (Or.inr (by omega)) hz3delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct3 := piQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by omega) (by omega)
  have hq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct3.symm.trans hq3
  have hdp4 : A.natDegree < 4 * A.natDegree + 3 * B.natDegree := by
    omega
  have hdz4 : 0 < 4 * A.natDegree + 3 * B.natDegree := by omega
  have hz4l : l = 0 ∨ (8 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 5 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree + G.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbl with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz4beta : beta = 0 ∨ (7 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbbeta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz4delta : delta = 0 ∨ (6 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 3 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 4 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz4zeta : zeta = 0 ∨ (5 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ B.natDegree + F.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hz4theta : theta = 0 ∨ (4 * A.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ A.natDegree + 2 * B.natDegree < 4 * A.natDegree + 3 * B.natDegree ∧ G.natDegree < 4 * A.natDegree + 3 * B.natDegree) := by
    rcases hnbtheta with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
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
  have hr4 : (primitiveQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * A.natDegree + 3 * B.natDegree :=
    primitiveQuarticChamberRest6000810_natDegree_lt_of_live_BFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz4 hCz hDz hEz (by omega) (by omega) (by omega) (by omega) (by omega) hz4l hz4beta (Or.inr (by omega)) hz4delta (Or.inr (by omega)) hz4zeta (Or.inr (by omega)) hz4theta
  have hct4 := primitiveQuarticChamberFace6000810_coeff_top hAne hBne hGne (C := C) (D := D) (E := E) (F := F) (by omega)
  have hq4 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hprim]
    omega
  rw [degreeZeroPrimitiveQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr4,
    add_zero] at hq4
  have hin4 : (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff = 0 :=
    hct4.symm.trans hq4
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemBFG8810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hin4 hBc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CDG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDG2810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : c * g ^ 2 = 0 := by
    linear_combination ((3 / 5 : k) * c ^ 2 + (8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * c) * hr1
  exact (mul_ne_zero hCc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCDG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    omega
  have hdz0 : 0 < 3 * C.natDegree := by omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hEz hFz (by omega) hz0l hz0beta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    omega
  have hdz1 : 0 < 4 * C.natDegree := by omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hEz hFz (by omega) hz1l hz1beta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega) (by omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemCDG2810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CDG` / `CG·DD·CCC`: the 4 face rows force `a * d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCDG4810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr2 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr3 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hAc : (a : k) ≠ 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : a * d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * a * c * d) * hr0 + ((18 / 55 : k) * a * d) * hr1 + ((16 / 11 : k) * c ^ 2 + (-1664 / 165 : k) * g) * hr2
  exact (mul_ne_zero (mul_ne_zero hAc hDc) (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CDG` / `CG·DD·CCC` dies on the 4-carrier system (μ, π, N₃, N₄). -/
theorem quarticChamberCDG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCDG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDne, hEz, hFz, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨h5bl, h5bbeta, h5bdelta, h5bzeta, h5btheta⟩ :=
    quarticSigmaN5CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA homi hnu hkap
  have hdp0 : 0 < A.natDegree + 2 * D.natDegree := by
    omega
  have hdz0 : 0 < A.natDegree + 2 * D.natDegree := by omega
  have hz0l : l = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0delta : delta = 0 ∨ (A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr0 : (muQuarticChamberRest6003810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest6003810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hEz hFz hz0l hz0beta (Or.inr (by omega)) hz0delta (Or.inr (by omega)) (Or.inr (by omega))
  have hct0 := muQuarticChamberFace6003810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6003_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    omega
  have hdz1 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by omega
  have hz1l : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr1 : (piQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest6004810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hEz hFz hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := piQuarticChamberFace6004810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega) (by omega) (by omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hdp2 : A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree := by
    omega
  have hdz2 : 0 < A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz2l : l = 0 ∨ (7 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz2beta : beta = 0 ∨ (6 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz2delta : delta = 0 ∨ (5 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz2zeta : zeta = 0 ∨ (4 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz2theta : theta = 0 ∨ (3 * A.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree < A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hr2 : (n3QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * C.natDegree + D.natDegree :=
    n3QuarticChamberRest6000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hEz hFz (by omega) hz2l hz2beta (Or.inr (by omega)) hz2delta (Or.inr (by omega)) hz2zeta (Or.inr (by omega)) hz2theta
  have hct2 := n3QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega)
  have hq2 : (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN3Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos homi hnu
    omega
  rw [degreeZeroN3Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (45 / 2048 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct2.symm.trans hq2
  have hdp3 : A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by
    omega
  have hdz3 : 0 < 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by omega
  have hz3l : l = 0 ∨ (8 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 6 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3beta : beta = 0 ∨ (7 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 5 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ C.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3delta : delta = 0 ∨ (6 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 4 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
    rcases hkbdelta with h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz3zeta : zeta = 0 ∨ (5 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 3 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ A.natDegree + G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * D.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hz3theta : theta = 0 ∨ (4 * A.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ 2 * C.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree ∧ G.natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree) := by
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
  have hr3 : (n4QuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * A.natDegree + 2 * C.natDegree + D.natDegree :=
    n4QuarticChamberRest6000810_natDegree_lt_of_live_CDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz3 hBz hEz hFz (by omega) (by omega) (by omega) hz3l hz3beta (Or.inr (by omega)) hz3delta (Or.inr (by omega)) hz3zeta (Or.inr (by omega)) hz3theta
  have hct3 := n4QuarticChamberFace6000810_coeff_top hAne hCne hDne hGne (B := B) (E := E) (F := F) (by omega)
  have hq3 : (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * A.natDegree + 2 * C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hle := degreeZeroN4Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
      A B C D E F G hApos hprim homi
    omega
  rw [degreeZeroN4Quartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hq3
  have hin3 : (-15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff = 0 :=
    hct3.symm.trans hq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemCDG4810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hDc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CEG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCEG2810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : c * g ^ 2 = 0 := by
    linear_combination ((3 / 5 : k) * c ^ 2 + (8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * c) * hr1
  exact (mul_ne_zero hCc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCEG2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  have hdp0 : 0 < 3 * C.natDegree := by
    omega
  have hdz0 : 0 < 3 * C.natDegree := by omega
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hDz hFz (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    omega
  have hdz1 : 0 < 4 * C.natDegree := by omega
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hDz hFz (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega) (by omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemCEG2810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CEG` / `CG·EE·CCC`: the 3 face rows force `e * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCEG4810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g + (5 / 32 : k) * e ^ 2 = 0)
    (hr1 : (-15 / 128 : k) * c ^ 2 * e + (5 / 16 : k) * e * g = 0)
    (hr2 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (-5 / 8 : k) * c * e ^ 2 + (5 / 4 : k) * g ^ 2 = 0)
    (hEc : (e : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : e * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * e) * hr0 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr1 + ((18 / 55 : k) * e) * hr2
  exact (mul_ne_zero hEc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CEG` / `CG·EE·CCC` dies on the 3-carrier system (μ, ξ, π). -/
theorem quarticChamberCEG4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEG4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFz, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  have hdp0 : 0 < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hdz0 : 0 < 3 * C.natDegree := by omega
  have hh0 : 2 * C.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh1 : G.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh2 : E.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh3 : C.natDegree < 3 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hr0 : (muQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6004810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hDz hFz (Or.inr ⟨hh0, hh1⟩) (Or.inr hh2) (Or.inr hh3)
  have hct0 := muQuarticChamberFace6004810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by omega) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6004_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff + (5 / 32 : k) * E.leadingCoeff ^ 2 = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hdz1 : 0 < 2 * C.natDegree + E.natDegree := by omega
  have hh4 : C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh5 : 2 * C.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh6 : G.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh7 : E.natDegree < 2 * C.natDegree + E.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hr1 : (xiQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest6000810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hDz hFz (Or.inr hh4) (Or.inr ⟨hh5, hh6⟩) (Or.inr hh7)
  have hct1 := xiQuarticChamberFace6000810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by omega)
  have hq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxiDeg]
    omega
  rw [degreeZeroXiQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff = 0 :=
    hct1.symm.trans hq1
  have hdp2 : 0 < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hdz2 : 0 < 4 * C.natDegree := by omega
  have hh8 : 3 * C.natDegree < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh9 : 2 * E.natDegree < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh10 : C.natDegree + E.natDegree < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh11 : 2 * C.natDegree < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hh12 : G.natDegree < 4 * C.natDegree := by
    by_contra hcon
    exact hnc (by omega)
  have hr2 : (piQuarticChamberRest6005810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6005810_natDegree_lt_of_live_CEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz2 hBz hDz hFz (Or.inr ⟨hh8, hh9⟩) (Or.inr hh10) (Or.inr ⟨hh11, hh12⟩)
  have hct2 := piQuarticChamberFace6005810_coeff_top hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by omega) (by omega) (by omega)
  have hq2 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6005_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hq2
  have hin2 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (-5 / 8 : k) * C.leadingCoeff * E.leadingCoeff ^ 2 + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct2.symm.trans hq2
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemCEG4810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hEc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `CFG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemCFG8810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : c * g ^ 2 = 0 := by
    linear_combination ((3 / 5 : k) * c ^ 2 + (8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * c) * hr1
  exact (mul_ne_zero hCc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `CFG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberCFG8810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCFG8810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBz, hCne, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    omega
  have hdz0 : 0 < 3 * C.natDegree := by omega
  have hz0l : l = 0 ∨ (2 * A.natDegree + F.natDegree < 3 * C.natDegree ∧ C.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (A.natDegree + F.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hBz hDz hEz hz0l hz0beta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    omega
  have hdz1 : 0 < 4 * C.natDegree := by omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + F.natDegree < 4 * C.natDegree ∧ F.natDegree + G.natDegree < 4 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + F.natDegree < 4 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < 4 * C.natDegree ∧ C.natDegree + F.natDegree < 4 * C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_CFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hBz hDz hEz (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega) (by omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemCFG8810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc hGc

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDG` / `CG·CCC`: the 2 face rows force `c * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDG16810_cert
    (a b c d e f g : k)
    (hr0 : (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr1 : (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hCc : (c : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : c * g ^ 2 = 0 := by
    linear_combination ((3 / 5 : k) * c ^ 2 + (8 / 5 : k) * g) * hr0 + ((2 / 5 : k) * c) * hr1
  exact (mul_ne_zero hCc (pow_ne_zero 2 hGc)) ht

set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDG` / `CG·CCC` dies on the 2-carrier system (μ, π). -/
theorem quarticChamberBCDG16810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCDG16810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hdp0 : 0 < 3 * C.natDegree := by
    omega
  have hdz0 : 0 < 3 * C.natDegree := by omega
  have hz0l : l = 0 ∨ (4 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 3 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 3 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 3 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 3 * C.natDegree ∧ B.natDegree + G.natDegree < 3 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ 2 * A.natDegree + D.natDegree < 3 * C.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 3 * C.natDegree ∧ 3 * B.natDegree < 3 * C.natDegree ∧ C.natDegree + D.natDegree < 3 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz0delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < 3 * C.natDegree ∧ A.natDegree + D.natDegree < 3 * C.natDegree ∧ B.natDegree + C.natDegree < 3 * C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr0 : (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 3 * C.natDegree :=
    muQuarticChamberRest6000810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz0 hEz hFz (by omega) (by omega) (by omega) (by omega) hz0l hz0beta (Or.inr (by omega)) hz0delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct0 := muQuarticChamberFace6000810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega)
  have hq0 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (3 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmuDeg]
    omega
  rw [degreeZeroMuQuartic810_eq_face6000_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hq0
  have hin0 : (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff = 0 :=
    hct0.symm.trans hq0
  have hdp1 : 0 < 4 * C.natDegree := by
    omega
  have hdz1 : 0 < 4 * C.natDegree := by omega
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ 5 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 3 * C.natDegree < 4 * C.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < 4 * C.natDegree ∧ 3 * D.natDegree < 4 * C.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 4 * C.natDegree ∧ 3 * B.natDegree + C.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * D.natDegree < 4 * C.natDegree ∧ 2 * C.natDegree + D.natDegree < 4 * C.natDegree) := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < 4 * C.natDegree ∧ A.natDegree + 3 * B.natDegree < 4 * C.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 4 * C.natDegree ∧ 2 * B.natDegree + D.natDegree < 4 * C.natDegree ∧ B.natDegree + 2 * C.natDegree < 4 * C.natDegree) := by
    rcases hbdelta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hr1 : (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 4 * C.natDegree :=
    piQuarticChamberRest6001810_natDegree_lt_of_live_BCDG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdz1 hEz hFz (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz1l hz1beta (Or.inr (by omega)) hz1delta (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  have hct1 := piQuarticChamberFace6001810_coeff_top hCne hGne (A := A) (B := B) (D := D) (E := E) (F := F) (by omega) (by omega)
  have hq1 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (4 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpiDeg]
    omega
  rw [degreeZeroPiQuartic810_eq_face6001_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hq1
  have hin1 : (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 = 0 :=
    hct1.symm.trans hq1
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticUnownedSystemBCDG16810_cert A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hCc hGc


end QuarticChamberUnownedSystems3810

end Max11DegreeRoutes
